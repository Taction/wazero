package sysfs

import (
	"io"
	"io/fs"
	"os"
	"syscall"

	"github.com/tetratelabs/wazero/internal/fsapi"
	"github.com/tetratelabs/wazero/internal/platform"
)

func NewStdioFile(stdin bool, f fs.File) (fsapi.File, error) {
	// Return constant stat, which has fake times, but keep the underlying
	// file mode. Fake times are needed to pass wasi-testsuite.
	// https://github.com/WebAssembly/wasi-testsuite/blob/af57727/tests/rust/src/bin/fd_filestat_get.rs#L1-L19
	var mode fs.FileMode
	if st, err := f.Stat(); err != nil {
		return nil, err
	} else {
		mode = st.Mode()
	}
	var flag int
	if stdin {
		flag = syscall.O_RDONLY
	} else {
		flag = syscall.O_WRONLY
	}
	var file fsapi.File
	if of, ok := f.(*os.File); ok {
		// This is ok because functions that need path aren't used by stdioFile
		file = newOsFile("", flag, 0, of)
	} else {
		file = &fsFile{file: f}
	}
	return &stdioFile{File: file, st: fsapi.Stat_t{Mode: mode, Nlink: 1}}, nil
}

func OpenFile(path string, flag int, perm fs.FileMode) (*os.File, syscall.Errno) {
	if flag&fsapi.O_DIRECTORY != 0 && flag&(syscall.O_WRONLY|syscall.O_RDWR) != 0 {
		return nil, syscall.EISDIR // invalid to open a directory writeable
	}
	return openFile(path, flag, perm)
}

func OpenOSFile(path string, flag int, perm fs.FileMode) (fsapi.File, syscall.Errno) {
	f, errno := OpenFile(path, flag, perm)
	if errno != 0 {
		return nil, errno
	}
	return newOsFile(path, flag, perm, f), 0
}

func OpenFSFile(fs fs.FS, path string, flag int, perm fs.FileMode) (fsapi.File, syscall.Errno) {
	if flag&fsapi.O_DIRECTORY != 0 && flag&(syscall.O_WRONLY|syscall.O_RDWR) != 0 {
		return nil, syscall.EISDIR // invalid to open a directory writeable
	}
	f, err := fs.Open(path)
	if errno := platform.UnwrapOSError(err); errno != 0 {
		return nil, errno
	}
	// Don't return an os.File because the path is not absolute. osFile needs
	// the path to be real and certain fs.File impls are subrooted.
	return &fsFile{fs: fs, name: path, file: f}, 0
}

type stdioFile struct {
	fsapi.File
	st fsapi.Stat_t
}

// SetAppend implements File.SetAppend
func (f *stdioFile) SetAppend(bool) syscall.Errno {
	// Ignore for stdio.
	return 0
}

// IsAppend implements File.SetAppend
func (f *stdioFile) IsAppend() bool {
	return true
}

// Stat implements File.Stat
func (f *stdioFile) Stat() (fsapi.Stat_t, syscall.Errno) {
	return f.st, 0
}

// Close implements File.Close
func (f *stdioFile) Close() syscall.Errno {
	return 0
}

// fsFile is used for wrapped fs.File, like os.Stdin or any fs.File
// implementation. Notably, this does not have access to the full file path.
// so certain operations can't be supported, such as inode lookups on Windows.
type fsFile struct {
	fsapi.UnimplementedFile

	// fs is the file-system that opened the file, or nil when wrapped for
	// pre-opens like stdio.
	fs fs.FS

	// name is what was used in fs for Open, so it may not be the actual path.
	name string

	// file is always set, possibly an os.File like os.Stdin.
	file fs.File

	// reopenDir is true if reopen should be called before Readdir. This flag
	// is deferred until Readdir to prevent redundant rewinds. This could
	// happen if Seek(0) was called twice, or if in Windows, Seek(0) was called
	// before Readdir.
	reopenDir bool

	// closed is true when closed was called. This ensures proper syscall.EBADF
	closed bool

	// cachedStat includes fields that won't change while a file is open.
	cachedSt *cachedStat
}

type cachedStat struct {
	// dev is the same as fsapi.Stat_t Dev.
	dev uint64

	// dev is the same as fsapi.Stat_t Ino.
	ino fsapi.Ino

	// isDir is fsapi.Stat_t Mode masked with fs.ModeDir
	isDir bool
}

// cachedStat returns the cacheable parts of fsapi.Stat_t or an error if they
// couldn't be retrieved.
func (f *fsFile) cachedStat() (dev uint64, ino fsapi.Ino, isDir bool, errno syscall.Errno) {
	if f.cachedSt == nil {
		if _, errno = f.Stat(); errno != 0 {
			return
		}
	}
	return f.cachedSt.dev, f.cachedSt.ino, f.cachedSt.isDir, 0
}

// Dev implements the same method as documented on fsapi.File
func (f *fsFile) Dev() (uint64, syscall.Errno) {
	dev, _, _, errno := f.cachedStat()
	return dev, errno
}

// Ino implements the same method as documented on fsapi.File
func (f *fsFile) Ino() (fsapi.Ino, syscall.Errno) {
	_, ino, _, errno := f.cachedStat()
	return ino, errno
}

// IsDir implements the same method as documented on fsapi.File
func (f *fsFile) IsDir() (bool, syscall.Errno) {
	_, _, isDir, errno := f.cachedStat()
	return isDir, errno
}

// IsAppend implements the same method as documented on fsapi.File
func (f *fsFile) IsAppend() bool {
	return false
}

// SetAppend implements the same method as documented on fsapi.File
func (f *fsFile) SetAppend(bool) (errno syscall.Errno) {
	return fileError(f, f.closed, syscall.ENOSYS)
}

// Stat implements the same method as documented on fsapi.File
func (f *fsFile) Stat() (fsapi.Stat_t, syscall.Errno) {
	if f.closed {
		return fsapi.Stat_t{}, syscall.EBADF
	}

	st, errno := statFile(f.file)
	switch errno {
	case 0:
		f.cachedSt = &cachedStat{dev: st.Dev, ino: st.Ino, isDir: st.Mode&fs.ModeDir == fs.ModeDir}
	case syscall.EIO:
		errno = syscall.EBADF
	}
	return st, errno
}

// Read implements the same method as documented on fsapi.File
func (f *fsFile) Read(buf []byte) (n int, errno syscall.Errno) {
	if n, errno = read(f.file, buf); errno != 0 {
		// Defer validation overhead until we've already had an error.
		errno = fileError(f, f.closed, errno)
	}
	return
}

// Pread implements the same method as documented on fsapi.File
func (f *fsFile) Pread(buf []byte, off int64) (n int, errno syscall.Errno) {
	if ra, ok := f.file.(io.ReaderAt); ok {
		if n, errno = pread(ra, buf, off); errno != 0 {
			// Defer validation overhead until we've already had an error.
			errno = fileError(f, f.closed, errno)
		}
		return
	}

	// See /RATIONALE.md "fd_pread: io.Seeker fallback when io.ReaderAt is not supported"
	if rs, ok := f.file.(io.ReadSeeker); ok {
		// Determine the current position in the file, as we need to revert it.
		currentOffset, err := rs.Seek(0, io.SeekCurrent)
		if err != nil {
			return 0, fileError(f, f.closed, platform.UnwrapOSError(err))
		}

		// Put the read position back when complete.
		defer func() { _, _ = rs.Seek(currentOffset, io.SeekStart) }()

		// If the current offset isn't in sync with this reader, move it.
		if off != currentOffset {
			if _, err = rs.Seek(off, io.SeekStart); err != nil {
				return 0, fileError(f, f.closed, platform.UnwrapOSError(err))
			}
		}

		n, err = rs.Read(buf)
		if errno = platform.UnwrapOSError(err); errno != 0 {
			// Defer validation overhead until we've already had an error.
			errno = fileError(f, f.closed, errno)
		}
	} else {
		errno = syscall.ENOSYS // unsupported
	}
	return
}

// Seek implements the same method as documented on fsapi.File
func (f *fsFile) Seek(offset int64, whence int) (newOffset int64, errno syscall.Errno) {
	// If this is a directory, and we're attempting to seek to position zero,
	// we have to re-open the file to ensure the directory state is reset.
	var isDir bool
	if offset == 0 && whence == io.SeekStart {
		if isDir, errno = f.IsDir(); errno == 0 && isDir {
			f.reopenDir = true
			return
		}
	}

	if s, ok := f.file.(io.Seeker); ok {
		if newOffset, errno = seek(s, offset, whence); errno != 0 {
			// Defer validation overhead until we've already had an error.
			errno = fileError(f, f.closed, errno)
		}
	} else {
		errno = syscall.ENOSYS // unsupported
	}
	return
}

// Readdir implements the same method as documented on fsapi.File
//
// Notably, this uses readdirFile or fs.ReadDirFile if available. This does not
// return inodes on windows.
func (f *fsFile) Readdir(n int) (dirents []fsapi.Dirent, errno syscall.Errno) {
	// Windows lets you Readdir after close, fs.File also may not implement
	// close in a meaningful way. read our closed field to return consistent
	// results.
	if f.closed {
		errno = syscall.EBADF
		return
	}

	if f.reopenDir { // re-open the directory if needed.
		f.reopenDir = false
		if errno = adjustReaddirErr(f, f.closed, f.reopen()); errno != 0 {
			return
		}
	}

	if of, ok := f.file.(readdirFile); ok {
		// We can't use f.name here because it is the path up to the fsapi.FS,
		// not necessarily the real path. For this reason, Windows may not be
		// able to populate inodes. However, Darwin and Linux will.
		if dirents, errno = readdir(of, "", n); errno != 0 {
			errno = adjustReaddirErr(f, f.closed, errno)
		}
		return
	}

	// Try with fs.ReadDirFile which is available on api.FS implementations
	// like embed:fs.
	if rdf, ok := f.file.(fs.ReadDirFile); ok {
		entries, e := rdf.ReadDir(n)
		if errno = adjustReaddirErr(f, f.closed, e); errno != 0 {
			return
		}
		dirents = make([]fsapi.Dirent, 0, len(entries))
		for _, e := range entries {
			// By default, we don't attempt to read inode data
			dirents = append(dirents, fsapi.Dirent{Name: e.Name(), Type: e.Type()})
		}
	} else {
		errno = syscall.EBADF // not a directory
	}
	return
}

// Write implements the same method as documented on fsapi.File.
func (f *fsFile) Write(buf []byte) (n int, errno syscall.Errno) {
	if w, ok := f.file.(io.Writer); ok {
		if n, errno = write(w, buf); errno != 0 {
			// Defer validation overhead until we've already had an error.
			errno = fileError(f, f.closed, errno)
		}
	} else {
		errno = syscall.ENOSYS // unsupported
	}
	return
}

// Pwrite implements the same method as documented on fsapi.File.
func (f *fsFile) Pwrite(buf []byte, off int64) (n int, errno syscall.Errno) {
	if wa, ok := f.file.(io.WriterAt); ok {
		if n, errno = pwrite(wa, buf, off); errno != 0 {
			// Defer validation overhead until we've already had an error.
			errno = fileError(f, f.closed, errno)
		}
	} else {
		errno = syscall.ENOSYS // unsupported
	}
	return
}

// Close implements the same method as documented on fsapi.File.
func (f *fsFile) Close() syscall.Errno {
	if f.closed {
		return 0
	}
	f.closed = true
	return f.close()
}

func (f *fsFile) close() syscall.Errno {
	return platform.UnwrapOSError(f.file.Close())
}

// dirError is used for commands that work against a directory, but not a file.
func dirError(f fsapi.File, isClosed bool, errno syscall.Errno) syscall.Errno {
	if vErrno := validate(f, isClosed, false, true); vErrno != 0 {
		return vErrno
	}
	return errno
}

// fileError is used for commands that work against a file, but not a directory.
func fileError(f fsapi.File, isClosed bool, errno syscall.Errno) syscall.Errno {
	if vErrno := validate(f, isClosed, true, false); vErrno != 0 {
		return vErrno
	}
	return errno
}

// validate is used to making syscalls which will fail.
func validate(f fsapi.File, isClosed, wantFile, wantDir bool) syscall.Errno {
	if isClosed {
		return syscall.EBADF
	}

	isDir, errno := f.IsDir()
	if errno != 0 {
		return errno
	}

	if wantFile && isDir {
		return syscall.EISDIR
	} else if wantDir && !isDir {
		return syscall.ENOTDIR
	}
	return 0
}

func read(r io.Reader, buf []byte) (n int, errno syscall.Errno) {
	if len(buf) == 0 {
		return 0, 0 // less overhead on zero-length reads.
	}

	n, err := r.Read(buf)
	return n, platform.UnwrapOSError(err)
}

func pread(ra io.ReaderAt, buf []byte, off int64) (n int, errno syscall.Errno) {
	if len(buf) == 0 {
		return 0, 0 // less overhead on zero-length reads.
	}

	n, err := ra.ReadAt(buf, off)
	return n, platform.UnwrapOSError(err)
}

func seek(s io.Seeker, offset int64, whence int) (int64, syscall.Errno) {
	if uint(whence) > io.SeekEnd {
		return 0, syscall.EINVAL // negative or exceeds the largest valid whence
	}

	newOffset, err := s.Seek(offset, whence)
	return newOffset, platform.UnwrapOSError(err)
}

// reopenFile allows re-opening a file for reasons such as applying flags or
// directory iteration.
type reopenFile func() syscall.Errno

// compile-time check to ensure fsFile.reopen implements reopenFile.
var _ reopenFile = (*fsFile)(nil).reopen

// reopen implements the same method as documented on reopenFile.
func (f *fsFile) reopen() syscall.Errno {
	_ = f.close()
	var err error
	f.file, err = f.fs.Open(f.name)
	return platform.UnwrapOSError(err)
}

// readdirFile allows masking the `Readdir` function on os.File.
type readdirFile interface {
	Readdir(n int) ([]fs.FileInfo, error)
}

// readdir uses readdirFile.Readdir, special casing windows when path !="".
func readdir(f readdirFile, path string, n int) (dirents []fsapi.Dirent, errno syscall.Errno) {
	fis, e := f.Readdir(n)
	if errno = platform.UnwrapOSError(e); errno != 0 {
		return
	}

	dirents = make([]fsapi.Dirent, 0, len(fis))

	// linux/darwin won't have to fan out to lstat, but windows will.
	var ino fsapi.Ino
	for fi := range fis {
		t := fis[fi]
		if ino, errno = inoFromFileInfo(path, t); errno != 0 {
			return
		}
		dirents = append(dirents, fsapi.Dirent{Name: t.Name(), Ino: ino, Type: t.Mode().Type()})
	}
	return
}

func write(w io.Writer, buf []byte) (n int, errno syscall.Errno) {
	if len(buf) == 0 {
		return 0, 0 // less overhead on zero-length writes.
	}

	n, err := w.Write(buf)
	return n, platform.UnwrapOSError(err)
}

func pwrite(w io.WriterAt, buf []byte, off int64) (n int, errno syscall.Errno) {
	if len(buf) == 0 {
		return 0, 0 // less overhead on zero-length writes.
	}

	n, err := w.WriteAt(buf, off)
	return n, platform.UnwrapOSError(err)
}
