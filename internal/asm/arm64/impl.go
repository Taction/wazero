package asm_arm64

import (
	"bytes"
	"fmt"

	"github.com/tetratelabs/wazero/internal/asm"
)

type NodeImpl struct {
	// NOTE: fields here are exported for testing with the amd64_debug package.

	Instruction asm.Instruction

	OffsetInBinaryField asm.NodeOffsetInBinary // Field suffix to dodge conflict with OffsetInBinary

	// JumpTarget holds the target node in the linked for the jump-kind instruction.
	JumpTarget *NodeImpl
	Flag       NodeFlag
	// next holds the next node from this node in the assembled linked list.
	Next *NodeImpl

	Types                            OperandTypes
	SrcReg, SrcReg2, DstReg, DstReg2 asm.Register
	SrcConst, DstConst               asm.ConstantValue

	Mode byte

	// readInstructionAddressBeforeTargetInstruction holds the instruction right before the target of
	// read instruction address instruction. See asm.assemblerBase.CompileReadInstructionAddress.
	readInstructionAddressBeforeTargetInstruction asm.Instruction

	// JumpOrigins hold all the nodes trying to jump into this node. In other words, all the nodes with .JumpTarget == this.
	JumpOrigins map[*NodeImpl]struct{}
}

type NodeFlag byte

const (
	// NodeFlagInitializedForEncoding is always set to indicate that node is already initialized. Notably, this is used to judge
	// whether a jump is backward or forward before encoding.
	NodeFlagInitializedForEncoding NodeFlag = (1 << iota)
	NodeFlagBackwardJump
)

func (n *NodeImpl) isInitializedForEncoding() bool {
	return n.Flag&NodeFlagInitializedForEncoding != 0
}

func (n *NodeImpl) isJumpNode() bool {
	return n.JumpTarget != nil
}

func (n *NodeImpl) isBackwardJump() bool {
	return n.isJumpNode() && (n.Flag&NodeFlagBackwardJump != 0)
}

func (n *NodeImpl) isForwardJump() bool {
	return n.isJumpNode() && (n.Flag&NodeFlagBackwardJump == 0)
}

// AssignJumpTarget implements asm.Node.AssignJumpTarget.
func (n *NodeImpl) AssignJumpTarget(target asm.Node) {
	n.JumpTarget = target.(*NodeImpl)
}

// AssignSourceConstant implements asm.Node.AssignSourceConstant.
func (n *NodeImpl) AssignDestinationConstant(value asm.ConstantValue) {
	n.DstConst = value
}

// AssignSourceConstant implements asm.Node.AssignSourceConstant.
func (n *NodeImpl) AssignSourceConstant(value asm.ConstantValue) {
	n.SrcConst = value
}

// OffsetInBinary implements asm.Node.OffsetInBinary.
func (n *NodeImpl) OffsetInBinary() asm.NodeOffsetInBinary {
	return n.OffsetInBinaryField
}

// String implements fmt.Stringer.
//
// This is for debugging purpose, and the format is similar to the AT&T assembly syntax,
// meaning that this should look like "INSTRUCTION ${from}, ${to}" where each operand
// might be embraced by '[]' to represent the memory location, and multiple operands
// are embraced by `()`.
func (n *NodeImpl) String() (ret string) {
	instName := InstructionName(n.Instruction)
	switch n.Types {
	case OperandTypesNoneToNone:
		ret = instName
	case OperandTypesNoneToRegister:
		ret = fmt.Sprintf("%s %s", instName, RegisterName(n.DstReg))
	case OperandTypesNoneToMemory:
		ret = fmt.Sprintf("%s [%s + 0x%x]", instName, RegisterName(n.DstReg), n.DstConst)
	case OperandTypesNoneToBranch:
		ret = fmt.Sprintf("%s {%v}", instName, n.JumpTarget)
	case OperandTypesRegisterToRegister:
		ret = fmt.Sprintf("%s %s, %s", instName, RegisterName(n.SrcReg), RegisterName(n.DstReg))
	case OperandTypesLeftShiftedRegisterToRegister:
		ret = fmt.Sprintf("%s (%s, %s << %d), %s", instName, RegisterName(n.SrcReg), RegisterName(n.SrcReg2), n.SrcConst, RegisterName(n.DstReg))
	case OperandTypesTwoRegistersToRegister:
		ret = fmt.Sprintf("%s (%s, %s), %s", instName, RegisterName(n.SrcReg), RegisterName(n.SrcReg2), RegisterName(n.DstReg))
	case OperandTypesTwoRegisters:
		ret = fmt.Sprintf("%s (%s, %s), (%s, %s)", instName, RegisterName(n.SrcReg), RegisterName(n.SrcReg2), RegisterName(n.DstReg), RegisterName(n.DstReg2))
	case OperandTypesTwoRegistersToNone:
		ret = fmt.Sprintf("%s (%s, %s)", instName, RegisterName(n.SrcReg), RegisterName(n.SrcReg2))
	case OperandTypesRegisterAndConstToNone:
		ret = fmt.Sprintf("%s (%s, 0x%x)", instName, RegisterName(n.SrcReg), n.SrcConst)
	case OperandTypesRegisterToMemory:
		if n.DstReg2 != asm.NilRegister {
			ret = fmt.Sprintf("%s %s, [%s + %s]", instName, RegisterName(n.SrcReg), RegisterName(n.DstReg), RegisterName(n.DstReg2))
		} else {
			ret = fmt.Sprintf("%s %s, [%s + 0x%d]", instName, RegisterName(n.SrcReg), RegisterName(n.DstReg), n.DstConst)
		}
	case OperandTypesMemoryToRegister:
		if n.SrcReg2 != asm.NilRegister {
			ret = fmt.Sprintf("%s [%s + %s], %s", instName, RegisterName(n.SrcReg), RegisterName(n.SrcReg2), RegisterName(n.DstReg))
		} else {
			ret = fmt.Sprintf("%s [%s + 0x%d], %s", instName, RegisterName(n.SrcReg), n.SrcConst, RegisterName(n.DstReg))
		}
	case OperandTypesConstToRegister:
		ret = fmt.Sprintf("%s 0x%d, %s", instName, n.SrcConst, RegisterName(n.DstReg))
	case OperandTypesSIMDByteToSIMDByte:
		ret = fmt.Sprintf("%s %s.B8, %s.B8", instName, RegisterName(n.SrcReg), RegisterName(n.DstReg))
	case OperandTypesSIMDByteToRegister:
		ret = fmt.Sprintf("%s %s.B8, %s", instName, RegisterName(n.SrcReg), RegisterName(n.DstReg))
	case OperandTypesTwoSIMDBytesToSIMDByteRegister:
		ret = fmt.Sprintf("%s (%s.B8, %s.B8), %s.B8", instName, RegisterName(n.SrcReg), RegisterName(n.SrcReg2), RegisterName(n.DstReg))
	}
	return
}

// OperandType represents where an operand is placed for an instruction.
// Note: this is almost the same as obj.AddrType in GO assembler.
type OperandType byte

const (
	OperandTypeNone OperandType = iota
	OperandTypeRegister
	OperandTypeLeftShiftedRegister
	OperandTypeTwoRegisters
	OperandTypeRegisterAndConst
	OperandTypeMemory
	OperandTypeConst
	OperandTypeBranch
	OperandTypeSIMDByte
	OperandTypeTwoSIMDBytes
)

func (o OperandType) String() (ret string) {
	switch o {
	case OperandTypeNone:
		ret = "none"
	case OperandTypeRegister:
		ret = "register"
	case OperandTypeLeftShiftedRegister:
		ret = "left-shifted-register"
	case OperandTypeTwoRegisters:
		ret = "two-registers"
	case OperandTypeRegisterAndConst:
		ret = "register-and-const"
	case OperandTypeMemory:
		ret = "memory"
	case OperandTypeConst:
		ret = "const"
	case OperandTypeBranch:
		ret = "branch"
	case OperandTypeSIMDByte:
		ret = "simd-byte"
	case OperandTypeTwoSIMDBytes:
		ret = "two-simd-bytes"
	}
	return
}

// OperandTypes represents the only combinations of two OperandTypes used by wazero
type OperandTypes struct{ src, dst OperandType }

var (
	OperandTypesNoneToNone                     = OperandTypes{OperandTypeNone, OperandTypeNone}
	OperandTypesNoneToRegister                 = OperandTypes{OperandTypeNone, OperandTypeRegister}
	OperandTypesNoneToMemory                   = OperandTypes{OperandTypeNone, OperandTypeMemory}
	OperandTypesNoneToBranch                   = OperandTypes{OperandTypeNone, OperandTypeBranch}
	OperandTypesRegisterToRegister             = OperandTypes{OperandTypeRegister, OperandTypeRegister}
	OperandTypesLeftShiftedRegisterToRegister  = OperandTypes{OperandTypeLeftShiftedRegister, OperandTypeRegister}
	OperandTypesTwoRegistersToRegister         = OperandTypes{OperandTypeTwoRegisters, OperandTypeRegister}
	OperandTypesTwoRegisters                   = OperandTypes{OperandTypeTwoRegisters, OperandTypeTwoRegisters}
	OperandTypesTwoRegistersToNone             = OperandTypes{OperandTypeTwoRegisters, OperandTypeNone}
	OperandTypesRegisterAndConstToNone         = OperandTypes{OperandTypeRegisterAndConst, OperandTypeNone}
	OperandTypesRegisterToMemory               = OperandTypes{OperandTypeRegister, OperandTypeMemory}
	OperandTypesMemoryToRegister               = OperandTypes{OperandTypeMemory, OperandTypeRegister}
	OperandTypesConstToRegister                = OperandTypes{OperandTypeConst, OperandTypeRegister}
	OperandTypesSIMDByteToSIMDByte             = OperandTypes{OperandTypeSIMDByte, OperandTypeSIMDByte}
	OperandTypesSIMDByteToRegister             = OperandTypes{OperandTypeSIMDByte, OperandTypeRegister}
	OperandTypesTwoSIMDBytesToSIMDByteRegister = OperandTypes{OperandTypeTwoSIMDBytes, OperandTypeSIMDByte}
)

// String implements fmt.Stringer
func (o OperandTypes) String() string {
	return fmt.Sprintf("from:%s,to:%s", o.src, o.dst)
}

// AssemblerImpl implements Assembler.
type AssemblerImpl struct {
	asm.BaseAssemblerImpl
	Root, Current     *NodeImpl
	Buf               *bytes.Buffer
	ForceReAssemble   bool
	temporaryRegister asm.Register
}

var _ Assembler = &AssemblerImpl{}

func NewAssemblerImpl(temporaryRegister asm.Register) *AssemblerImpl {
	return &AssemblerImpl{Buf: bytes.NewBuffer(nil)}
}

// newNode creates a new Node and appends it into the linked list.
func (a *AssemblerImpl) newNode(instruction asm.Instruction, types OperandTypes) *NodeImpl {
	n := &NodeImpl{
		Instruction: instruction,
		Next:        nil,
		Types:       types,
		JumpOrigins: map[*NodeImpl]struct{}{},
	}

	a.addNode(n)
	return n
}

// addNode appends the new node into the linked list.
func (a *AssemblerImpl) addNode(node *NodeImpl) {
	if a.Root == nil {
		a.Root = node
		a.Current = node
	} else {
		parent := a.Current
		parent.Next = node
		a.Current = node
	}

	for _, o := range a.SetBranchTargetOnNextNodes {
		origin := o.(*NodeImpl)
		origin.JumpTarget = node
	}
	a.SetBranchTargetOnNextNodes = nil
}

// Assemble implements asm.AssemblerBase
func (a *AssemblerImpl) Assemble() ([]byte, error) {
	a.InitializeNodesForEncoding()

	for n := a.Root; n != nil; n = n.Next {
		n.OffsetInBinaryField = (uint64(a.Buf.Len()))

		if err := a.EncodeNode(n); err != nil {
			return nil, fmt.Errorf("%w: %v", err, n)
		}

		if err := a.ResolveForwardRelativeJumps(n); err != nil {
			return nil, fmt.Errorf("invalid relative forward jumps: %w", err)
		}
	}

	code := a.Buf.Bytes()
	for _, cb := range a.OnGenerateCallbacks {
		if err := cb(code); err != nil {
			return nil, err
		}
	}
	return code, nil
}

// EncodeNode encodes the given node into writer.
func (a *AssemblerImpl) EncodeNode(n *NodeImpl) (err error) {
	switch n.Types {
	case OperandTypesNoneToNone:
		err = a.encodeNoneToNone(n)
	case OperandTypesNoneToRegister:
		err = a.encodeNoneToRegister(n)
	case OperandTypesNoneToMemory:
		err = a.encodeNoneToMemory(n)
	case OperandTypesNoneToBranch:
		err = a.encodeNoneToBranch(n)
	case OperandTypesRegisterToRegister:
		err = a.encodeRegisterToRegister(n)
	case OperandTypesLeftShiftedRegisterToRegister:
		err = a.encodeLeftShiftedRegisterToRegister(n)
	case OperandTypesTwoRegistersToRegister:
		err = a.encodeTwoRegistersToRegister(n)
	case OperandTypesTwoRegisters:
		err = a.encodeTwoRegisters(n)
	case OperandTypesTwoRegistersToNone:
		err = a.encodeTwoRegistersToNone(n)
	case OperandTypesRegisterAndConstToNone:
		err = a.encodeRegisterAndConstToNone(n)
	case OperandTypesRegisterToMemory:
		err = a.encodeRegisterToMemory(n)
	case OperandTypesMemoryToRegister:
		err = a.encodeMemoryToRegister(n)
	case OperandTypesConstToRegister:
		err = a.encodeConstToRegister(n)
	case OperandTypesSIMDByteToSIMDByte:
		err = a.encodeSIMDByteToSIMDByte(n)
	case OperandTypesSIMDByteToRegister:
		err = a.encodeSIMDByteToRegister(n)
	case OperandTypesTwoSIMDBytesToSIMDByteRegister:
		err = a.encodeTwoSIMDBytesToSIMDByteRegister(n)
	default:
		err = fmt.Errorf("encoder undefined for [%s] operand type", n.Types)
	}
	return
}

// InitializeNodesForEncoding initializes NodeImpl.Flag and determine all the jumps
// are forward or backward jump.
func (a *AssemblerImpl) InitializeNodesForEncoding() {
	var count int
	for n := a.Root; n != nil; n = n.Next {
		count++
		n.Flag |= NodeFlagInitializedForEncoding
		if target := n.JumpTarget; target != nil {
			if target.isInitializedForEncoding() {
				// This means the target exists behind.
				n.Flag |= NodeFlagBackwardJump
			}
		}
	}

	// arm64 has 32-bit fixed length instructions.
	a.Buf.Grow(count * 8)
}

func (a *AssemblerImpl) ResolveForwardRelativeJumps(target *NodeImpl) (err error) {
	// TODO: Maybe not necessary as ARM64 has fixed length instructions.
	return nil
}

// CompileStandAlone implements asm.AssemblerBase.CompileStandAlone
func (a *AssemblerImpl) CompileStandAlone(instruction asm.Instruction) asm.Node {
	return a.newNode(instruction, OperandTypesNoneToNone)
}

// CompileConstToRegister implements asm.AssemblerBase.CompileConstToRegister
func (a *AssemblerImpl) CompileConstToRegister(instruction asm.Instruction, value asm.ConstantValue, destinationReg asm.Register) (inst asm.Node) {
	n := a.newNode(instruction, OperandTypesConstToRegister)
	n.SrcConst = value
	n.DstReg = destinationReg
	return n
}

// CompileRegisterToRegister implements asm.AssemblerBase.CompileRegisterToRegister
func (a *AssemblerImpl) CompileRegisterToRegister(instruction asm.Instruction, from, to asm.Register) {
	n := a.newNode(instruction, OperandTypesRegisterToRegister)
	n.SrcReg = from
	n.DstReg = to
}

// CompileMemoryToRegister implements asm.AssemblerBase.CompileMemoryToRegister
func (a *AssemblerImpl) CompileMemoryToRegister(instruction asm.Instruction, sourceBaseReg asm.Register, sourceOffsetConst asm.ConstantValue, destinationReg asm.Register) {
	n := a.newNode(instruction, OperandTypesMemoryToRegister)
	n.SrcReg = sourceBaseReg
	n.SrcConst = sourceOffsetConst
	n.DstReg = destinationReg
}

// CompileRegisterToMemory implements asm.AssemblerBase.CompileRegisterToMemory
func (a *AssemblerImpl) CompileRegisterToMemory(instruction asm.Instruction, sourceRegister asm.Register, destinationBaseRegister asm.Register, destinationOffsetConst asm.ConstantValue) {
	n := a.newNode(instruction, OperandTypesRegisterToMemory)
	n.SrcReg = sourceRegister
	n.DstReg = destinationBaseRegister
	n.DstConst = destinationOffsetConst
}

// CompileJump implements asm.AssemblerBase.CompileJump
func (a *AssemblerImpl) CompileJump(jmpInstruction asm.Instruction) asm.Node {
	return a.newNode(jmpInstruction, OperandTypesNoneToBranch)
}

// CompileJumpToMemory implements asm.AssemblerBase.CompileJumpToMemory
func (a *AssemblerImpl) CompileJumpToMemory(jmpInstruction asm.Instruction, baseReg asm.Register, offset asm.ConstantValue) {
	n := a.newNode(jmpInstruction, OperandTypesNoneToMemory)
	n.DstReg = baseReg
	n.DstConst = offset
}

// CompileJumpToRegister implements asm.AssemblerBase.CompileJumpToRegister
func (a *AssemblerImpl) CompileJumpToRegister(jmpInstruction asm.Instruction, reg asm.Register) {
	n := a.newNode(jmpInstruction, OperandTypesNoneToRegister)
	n.DstReg = reg
}

// CompileReadInstructionAddress implements asm.AssemblerBase.CompileReadInstructionAddress
func (a *AssemblerImpl) CompileReadInstructionAddress(destinationRegister asm.Register, beforeAcquisitionTargetInstruction asm.Instruction) {
	n := a.newNode(ADR, OperandTypesMemoryToRegister)
	n.DstReg = destinationRegister
	n.readInstructionAddressBeforeTargetInstruction = beforeAcquisitionTargetInstruction
}

// CompileMemoryWithRegisterOffsetToRegister implements Assembler.CompileMemoryWithRegisterOffsetToRegister
func (a *AssemblerImpl) CompileMemoryWithRegisterOffsetToRegister(instruction asm.Instruction, srcBaseReg, srcOffsetReg, dstReg asm.Register) {
	n := a.newNode(instruction, OperandTypesMemoryToRegister)
	n.DstReg = dstReg
	n.SrcReg = srcBaseReg
	n.SrcReg2 = srcOffsetReg
}

// CompileRegisterToMemoryWithRegisterOffset implements Assembler.CompileRegisterToMemoryWithRegisterOffset
func (a *AssemblerImpl) CompileRegisterToMemoryWithRegisterOffset(instruction asm.Instruction, srcReg, dstBaseReg, dstOffsetReg asm.Register) {
	n := a.newNode(instruction, OperandTypesRegisterToMemory)
	n.SrcReg = srcReg
	n.DstReg = dstBaseReg
	n.DstReg2 = dstOffsetReg
}

// CompileTwoRegistersToRegister implements Assembler.CompileTwoRegistersToRegister
func (a *AssemblerImpl) CompileTwoRegistersToRegister(instruction asm.Instruction, src1, src2, dst asm.Register) {
	n := a.newNode(instruction, OperandTypesTwoRegistersToRegister)
	n.SrcReg = src1
	n.SrcReg2 = src2
	n.DstReg = dst
}

// CompileTwoRegisters implements Assembler.CompileTwoRegisters
func (a *AssemblerImpl) CompileTwoRegisters(instruction asm.Instruction, src1, src2, dst1, dst2 asm.Register) {
	n := a.newNode(instruction, OperandTypesTwoRegisters)
	n.SrcReg = src1
	n.SrcReg2 = src2
	n.DstReg = dst1
	n.DstReg2 = dst2
}

// CompileTwoRegistersToNone implements Assembler.CompileTwoRegistersToNone
func (a *AssemblerImpl) CompileTwoRegistersToNone(instruction asm.Instruction, src1, src2 asm.Register) {
	n := a.newNode(instruction, OperandTypesTwoRegistersToNone)
	n.SrcReg = src1
	n.SrcReg2 = src2
}

// CompileRegisterAndConstToNone implements Assembler.CompileRegisterAndConstToNone
func (a *AssemblerImpl) CompileRegisterAndConstToNone(instruction asm.Instruction, src asm.Register, srcConst asm.ConstantValue) {
	n := a.newNode(instruction, OperandTypesRegisterAndConstToNone)
	n.SrcReg = src
	n.SrcConst = srcConst
}

// CompileLeftShiftedRegisterToRegister implements Assembler.CompileLeftShiftedRegisterToRegister
func (a *AssemblerImpl) CompileLeftShiftedRegisterToRegister(instruction asm.Instruction, shiftedSourceReg asm.Register, shiftNum asm.ConstantValue, srcReg, dstReg asm.Register) {
	n := a.newNode(instruction, OperandTypesLeftShiftedRegisterToRegister)
	n.SrcReg = srcReg
	n.SrcReg2 = shiftedSourceReg
	n.SrcConst = shiftNum
	n.DstReg = dstReg
}

// CompileSIMDByteToSIMDByte implements Assembler.CompileSIMDByteToSIMDByte
func (a *AssemblerImpl) CompileSIMDByteToSIMDByte(instruction asm.Instruction, srcReg, dstReg asm.Register) {
	n := a.newNode(instruction, OperandTypesSIMDByteToSIMDByte)
	n.SrcReg = srcReg
	n.DstReg = dstReg
}

// CompileTwoSIMDBytesToSIMDByteRegister implements Assembler.CompileTwoSIMDBytesToSIMDByteRegister
func (a *AssemblerImpl) CompileTwoSIMDBytesToSIMDByteRegister(instruction asm.Instruction, srcReg1, srcReg2, dstReg asm.Register) {
	n := a.newNode(instruction, OperandTypesTwoSIMDBytesToSIMDByteRegister)
	n.SrcReg = srcReg1
	n.SrcReg2 = srcReg2
	n.DstReg = dstReg
}

// CompileSIMDByteToRegister implements Assembler.CompileSIMDByteToRegister
func (a *AssemblerImpl) CompileSIMDByteToRegister(instruction asm.Instruction, srcReg, dstReg asm.Register) {
	n := a.newNode(instruction, OperandTypesSIMDByteToRegister)
	n.SrcReg = srcReg
	n.DstReg = dstReg
}

// CompileConditionalRegisterSet implements Assembler.CompileConditionalRegisterSet
func (a *AssemblerImpl) CompileConditionalRegisterSet(cond asm.ConditionalRegisterState, dstReg asm.Register) {
	n := a.newNode(CSET, OperandTypesRegisterToRegister)
	n.SrcReg = conditionalRegisterStateToRegister(cond)
	n.DstReg = dstReg
}

func (a *AssemblerImpl) encodeNoneToNone(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeNoneToRegister(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeNoneToMemory(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeNoneToBranch(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeRegisterToRegister(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeLeftShiftedRegisterToRegister(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeTwoRegistersToRegister(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeTwoRegisters(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeTwoRegistersToNone(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeRegisterAndConstToNone(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeRegisterToMemory(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeMemoryToRegister(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeConstToRegister(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeSIMDByteToSIMDByte(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeSIMDByteToRegister(n *NodeImpl) (err error) {
	return
}

func (a *AssemblerImpl) encodeTwoSIMDBytesToSIMDByteRegister(n *NodeImpl) (err error) {
	return
}
