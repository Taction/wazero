package fsapi

import "io/fs"

// Stat_t is similar to syscall.Stat_t, and fields frequently used by
// WebAssembly ABI including wasip1 and wasi-filesystem (a.k.a. wasip2).
//
// # Note
//
// Zero values may be returned where not available. For example, fs.FileInfo
// implementations may not be able to provide Ino values.
type Stat_t struct {
	// Dev is the device ID of device containing the file.
	Dev uint64

	// Ino is the file serial number, or zero if not available. See Ino for
	// more details including impact returning a zero value.
	Ino Ino

	// Mode is the same as Mode on fs.FileInfo containing bits to identify the
	// type of the file (fs.ModeType) and its permissions (fs.ModePerm).
	Mode fs.FileMode

	/// Nlink is the number of hard links to the file.
	Nlink uint64
	// ^^ uint64 not uint16 to accept widest syscall.Stat_t.Nlink

	// Size is the length in bytes for regular files. For symbolic links, this
	// is length in bytes of the pathname contained in the symbolic link.
	Size int64
	// ^^ int64 not uint64 to defer to fs.FileInfo

	// Atim is the last data access timestamp in epoch nanoseconds.
	Atim int64

	// Mtim is the last data modification timestamp in epoch nanoseconds.
	Mtim int64

	// Ctim is the last file status change timestamp in epoch nanoseconds.
	Ctim int64
}
