package asm_arm64

import (
	"bytes"
	"errors"
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
	case OperandTypesThreeRegistersToRegister:
		ret = fmt.Sprintf("%s (%s, %s, %s), %s)", instName, RegisterName(n.SrcReg), RegisterName(n.SrcReg2), RegisterName(n.DstReg), RegisterName(n.DstReg2))
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
	OperandTypeThreeRegisters
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
	OperandTypesThreeRegistersToRegister       = OperandTypes{OperandTypeThreeRegisters, OperandTypeRegister}
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

	code := a.Bytes()
	for _, cb := range a.OnGenerateCallbacks {
		if err := cb(code); err != nil {
			return nil, err
		}
	}
	return code, nil
}

func (a *AssemblerImpl) Bytes() []byte {
	// 16 bytes alignment to line our impl with golang-asm.
	// TODO: delete later.
	if pad := 16 - a.Buf.Len()%16; pad > 0 {
		a.Buf.Write(make([]byte, pad))
	}
	return a.Buf.Bytes()
}

// EncodeNode encodes the given node into writer.
func (a *AssemblerImpl) EncodeNode(n *NodeImpl) (err error) {
	switch n.Types {
	case OperandTypesNoneToNone:
		err = a.EncodeNoneToNone(n)
	case OperandTypesNoneToRegister, OperandTypesNoneToMemory:
		err = a.EncodeJumpToRegister(n)
	case OperandTypesNoneToBranch:
		err = a.EncodeNoneToBranch(n)
	case OperandTypesRegisterToRegister:
		err = a.EncodeRegisterToRegister(n)
	case OperandTypesLeftShiftedRegisterToRegister:
		err = a.EncodeLeftShiftedRegisterToRegister(n)
	case OperandTypesTwoRegistersToRegister:
		err = a.EncodeTwoRegistersToRegister(n)
	case OperandTypesThreeRegistersToRegister:
		err = a.EncodeThreeRegistersToRegister(n)
	case OperandTypesTwoRegistersToNone:
		err = a.EncodeTwoRegistersToNone(n)
	case OperandTypesRegisterAndConstToNone:
		err = a.EncodeRegisterAndConstToNone(n)
	case OperandTypesRegisterToMemory:
		err = a.EncodeRegisterToMemory(n)
	case OperandTypesMemoryToRegister:
		err = a.EncodeMemoryToRegister(n)
	case OperandTypesConstToRegister:
		err = a.EncodeConstToRegister(n)
	case OperandTypesSIMDByteToSIMDByte:
		err = a.EncodeSIMDByteToSIMDByte(n)
	case OperandTypesSIMDByteToRegister:
		err = a.EncodeSIMDByteToRegister(n)
	case OperandTypesTwoSIMDBytesToSIMDByteRegister:
		err = a.EncodeTwoSIMDBytesToSIMDByteRegister(n)
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
func (a *AssemblerImpl) CompileJumpToMemory(jmpInstruction asm.Instruction, baseReg asm.Register) {
	n := a.newNode(jmpInstruction, OperandTypesNoneToMemory)
	n.DstReg = baseReg
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

// CompileTwoRegisters implements Assembler.CompileThreeRegistersToRegister
func (a *AssemblerImpl) CompileThreeRegistersToRegister(instruction asm.Instruction, src1, src2, src3, dst asm.Register) {
	n := a.newNode(instruction, OperandTypesThreeRegistersToRegister)
	n.SrcReg = src1
	n.SrcReg2 = src2
	n.DstReg = src3 // To minimize the size of NodeImpl struct, we reuse DstReg for the third source operand.
	n.DstReg2 = dst
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

func errorEncodingUnsupported(n *NodeImpl) error {
	return fmt.Errorf("%s is unsupported for %s type", InstructionName(n.Instruction), n.Types)
}

func (a *AssemblerImpl) EncodeNoneToNone(n *NodeImpl) (err error) {
	if n.Instruction != NOP {
		err = errorEncodingUnsupported(n)
	}
	return
}

func (a *AssemblerImpl) EncodeJumpToRegister(n *NodeImpl) (err error) {
	// "Unconditional branch (register)" in https://developer.arm.com/documentation/ddi0596/2021-12/Index-by-Encoding/Branches--Exception-Generating-and-System-instructions
	var opc byte
	switch n.Instruction {
	case RET:
		opc = 0b0010
	case B:
		opc = 0b0000
	default:
		return errorEncodingUnsupported(n)
	}

	regBits, err := intRegisterBits(n.DstReg)
	if err != nil {
		return fmt.Errorf("invalid destination register: %w", err)
	}

	a.Buf.Write([]byte{
		0x00 | (regBits << 5),
		0x00 | (regBits >> 3),
		0b000_11111 | (opc << 5),
		0b1101011_0 | (opc >> 3),
	})
	return
}

// encodeNoneToBranch:  B BRANCH_TARGET
// encodeNoneToBranch:  BEQ BRANCH_TARGET
// encodeNoneToBranch:  BGE BRANCH_TARGET
// encodeNoneToBranch:  BGT BRANCH_TARGET
// encodeNoneToBranch:  BHI BRANCH_TARGET
// encodeNoneToBranch:  BHS BRANCH_TARGET
// encodeNoneToBranch:  BLE BRANCH_TARGET
// encodeNoneToBranch:  BLO BRANCH_TARGET
// encodeNoneToBranch:  BLS BRANCH_TARGET
// encodeNoneToBranch:  BLT BRANCH_TARGET
// encodeNoneToBranch:  BMI BRANCH_TARGET
// encodeNoneToBranch:  BNE BRANCH_TARGET
// encodeNoneToBranch:  BVS BRANCH_TARGET
func (a *AssemblerImpl) EncodeNoneToBranch(n *NodeImpl) (err error) {
	return
}

func checkRegisterToRegisterType(src, dst asm.Register, requireSrcInt, requireDstInt bool) (err error) {
	isSrcInt, isDstInt := isIntRegister(src), isIntRegister(dst)
	if isSrcInt && !requireSrcInt {
		err = fmt.Errorf("src requires float register but got %s", RegisterName(src))
	} else if !isSrcInt && requireSrcInt {
		err = fmt.Errorf("src requires int register but got %s", RegisterName(src))
	} else if isDstInt && !requireDstInt {
		err = fmt.Errorf("dst requires float register but got %s", RegisterName(dst))
	} else if !isDstInt && requireDstInt {
		err = fmt.Errorf("dst requires int register but got %s", RegisterName(dst))
	}
	return
}

func (a *AssemblerImpl) EncodeRegisterToRegister(n *NodeImpl) (err error) {
	switch inst := n.Instruction; inst {
	case ADD, ADDW, SUB:
		if err = checkRegisterToRegisterType(n.SrcReg, n.DstReg, true, true); err != nil {
			return
		}

		// https://developer.arm.com/documentation/ddi0596/2021-12/Index-by-Encoding/Data-Processing----Register?lang=en#addsub_shift
		var sfops byte
		switch inst {
		case ADD:
			sfops = 0b100
		case ADDW:
		case SUB:
			sfops = 0b110
		}

		srcRegBits, dstRegBits := registerBits(n.SrcReg), registerBits(n.DstReg)
		a.Buf.Write([]byte{
			(dstRegBits << 5) | dstRegBits,
			(dstRegBits >> 3),
			srcRegBits,
			(sfops << 5) | 0b01011,
		})
	case CLZ, CLZW, RBIT, RBITW:
		if err = checkRegisterToRegisterType(n.SrcReg, n.DstReg, true, true); err != nil {
			return
		}

		var sf, opcode byte
		switch inst {
		case CLZ:
			sf, opcode = 0b1, 0b000_100
		case CLZW:
			sf, opcode = 0b0, 0b000_100
		case RBIT:
			sf, opcode = 0b1, 0b000_000
		case RBITW:
			sf, opcode = 0b0, 0b000_000
		}
		if inst == CLZ {
			sf = 1
		}

		srcRegBits, dstRegBits := registerBits(n.SrcReg), registerBits(n.DstReg)
		a.Buf.Write([]byte{
			(srcRegBits << 5) | dstRegBits,
			opcode<<2 | (srcRegBits >> 3),
			0b110_00000,
			(sf << 7) | 0b0_1011010,
		})
	case CSET:
		if !isConditionalRegister(n.SrcReg) {
			return fmt.Errorf("CSET requires conditional register but got %s", RegisterName(n.SrcReg))
		}

		dstRegBits, err := intRegisterBits(n.DstReg)
		if err != nil {
			return err
		}

		var conditionalBits byte
		switch n.SrcReg {
		case REG_COND_EQ:
			conditionalBits = 0b0001
		case REG_COND_NE:
			conditionalBits = 0b0000
		case REG_COND_HS:
			conditionalBits = 0b0011
		case REG_COND_LO:
			conditionalBits = 0b0010
		case REG_COND_MI:
			conditionalBits = 0b0101
		case REG_COND_PL:
			conditionalBits = 0b0100
		case REG_COND_VS:
			conditionalBits = 0b0111
		case REG_COND_VC:
			conditionalBits = 0b0110
		case REG_COND_HI:
			conditionalBits = 0b1001
		case REG_COND_LS:
			conditionalBits = 0b1000
		case REG_COND_GE:
			conditionalBits = 0b1011
		case REG_COND_LT:
			conditionalBits = 0b1010
		case REG_COND_GT:
			conditionalBits = 0b1101
		case REG_COND_LE:
			conditionalBits = 0b1100
		case REG_COND_AL:
			conditionalBits = 0b1111
		case REG_COND_NV:
			conditionalBits = 0b1110
		}

		// https://developer.arm.com/documentation/ddi0596/2021-12/Base-Instructions/CSET--Conditional-Set--an-alias-of-CSINC-?lang=en
		a.Buf.Write([]byte{
			0b111_00000 | dstRegBits,
			(conditionalBits << 4) | 0b0000_0111,
			0b100_11111,
			0b10011010,
		})

	case FABSD, FABSS, FNEGD, FNEGS, FSQRTD, FSQRTS, FCVTSD, FCVTDS, FRINTMD, FRINTMS,
		FRINTND, FRINTNS, FRINTPD, FRINTPS, FRINTZD, FRINTZS:
		if err = checkRegisterToRegisterType(n.SrcReg, n.DstReg, false, false); err != nil {
			return
		}

		srcRegBits, dstRegBits := registerBits(n.SrcReg), registerBits(n.DstReg)

		// https://developer.arm.com/documentation/ddi0596/2021-12/Index-by-Encoding/Data-Processing----Scalar-Floating-Point-and-Advanced-SIMD?lang=en#floatdp1
		var tp, opcode byte
		switch inst {
		case FABSD:
			opcode, tp = 0b000001, 0b01
		case FABSS:
			opcode, tp = 0b000001, 0b00
		case FNEGD:
			opcode, tp = 0b000010, 0b01
		case FNEGS:
			opcode, tp = 0b000010, 0b00
		case FSQRTD:
			opcode, tp = 0b000011, 0b01
		case FSQRTS:
			opcode, tp = 0b000011, 0b00
		case FCVTSD:
			opcode, tp = 0b000101, 0b00
		case FCVTDS:
			opcode, tp = 0b000100, 0b01
		case FRINTMD:
			opcode, tp = 0b001010, 0b01
		case FRINTMS:
			opcode, tp = 0b001010, 0b00
		case FRINTND:
			opcode, tp = 0b001000, 0b01
		case FRINTNS:
			opcode, tp = 0b001000, 0b00
		case FRINTPD:
			opcode, tp = 0b001001, 0b01
		case FRINTPS:
			opcode, tp = 0b001001, 0b00
		case FRINTZD:
			opcode, tp = 0b001011, 0b01
		case FRINTZS:
			opcode, tp = 0b001011, 0b00
		}
		a.Buf.Write([]byte{
			(srcRegBits << 5) | dstRegBits,
			(opcode << 7) | 0b0_10000_00 | (srcRegBits >> 3),
			tp<<6 | 0b00_1_00000 | opcode>>1,
			0b0_00_11110,
		})

	case FADDD, FADDS, FDIVS, FDIVD, FMAXD, FMAXS, FMIND, FMINS, FMULS, FMULD:
		if err = checkRegisterToRegisterType(n.SrcReg, n.DstReg, false, false); err != nil {
			return
		}

		srcRegBits, dstRegBits := registerBits(n.SrcReg), registerBits(n.DstReg)

		// "Floating-point data-processing (2 source)" in
		// https://developer.arm.com/documentation/ddi0596/2021-12/Index-by-Encoding/Data-Processing----Scalar-Floating-Point-and-Advanced-SIMD?lang=en#floatdp1
		var tp, opcode byte
		switch inst {
		case FADDD:
			opcode, tp = 0b0010, 0b01
		case FADDS:
			opcode, tp = 0b0010, 0b00
		case FDIVD:
			opcode, tp = 0b0001, 0b01
		case FDIVS:
			opcode, tp = 0b0001, 0b00
		case FMAXD:
			opcode, tp = 0b0100, 0b01
		case FMAXS:
			opcode, tp = 0b0100, 0b00
		case FMIND:
			opcode, tp = 0b0101, 0b01
		case FMINS:
			opcode, tp = 0b0101, 0b00
		case FMULS:
			opcode, tp = 0b0000, 0b00
		case FMULD:
			opcode, tp = 0b0000, 0b01
		}

		a.Buf.Write([]byte{
			(dstRegBits << 5) | dstRegBits,
			opcode<<4 | 0b0000_10_00 | (dstRegBits >> 3),
			tp<<6 | 0b00_1_00000 | srcRegBits,
			0b0001_1110,
		})

	case FCVTZSD, FCVTZSDW, FCVTZSS, FCVTZSSW, FCVTZUD, FCVTZUDW, FCVTZUS, FCVTZUSW:
		if err = checkRegisterToRegisterType(n.SrcReg, n.DstReg, false, true); err != nil {
			return
		}

		srcRegBits, dstRegBits := registerBits(n.SrcReg), registerBits(n.DstReg)

		// "Conversion between floating-point and integer" in
		// https://developer.arm.com/documentation/ddi0596/2021-12/Index-by-Encoding/Data-Processing----Scalar-Floating-Point-and-Advanced-SIMD?lang=en#floatdp1
		var sf, tp, opcode byte
		switch inst {
		case FCVTZSD: // Double to signed 64-bit
			sf, tp, opcode = 0b1, 0b01, 0b000
		case FCVTZSDW: // Double to signed 32-bit.
			sf, tp, opcode = 0b0, 0b01, 0b000
		case FCVTZSS: // Single to signed 64-bit.
			sf, tp, opcode = 0b1, 0b00, 0b000
		case FCVTZSSW: // Single to signed 32-bit.
			sf, tp, opcode = 0b0, 0b00, 0b000
		case FCVTZUD: // Dobule to unsigned 64-bit.
			sf, tp, opcode = 0b1, 0b01, 0b001
		case FCVTZUDW: // Double to unsigned 32-bit.
			sf, tp, opcode = 0b0, 0b01, 0b001
		case FCVTZUS: // Signle to unsigned 64-bit.
			sf, tp, opcode = 0b1, 0b00, 0b001
		case FCVTZUSW: // Signle to unsigned 32-bit.
			sf, tp, opcode = 0b0, 0b00, 0b001
		}

		a.Buf.Write([]byte{
			(srcRegBits << 5) | dstRegBits,
			0 | (srcRegBits >> 3),
			tp<<6 | 0b00_1_11_000 | opcode,
			sf<<7 | 0b0_0_0_11110,
		})

	case FMOVD, FMOVS:
		isSrcInt, isDstInt := isIntRegister(n.SrcReg), isIntRegister(n.DstReg)
		if isSrcInt && isDstInt {
			return errors.New("FMOV needs at least one of operands to be integer")
		}

		srcRegBits, dstRegBits := registerBits(n.SrcReg), registerBits(n.DstReg)
		if !isSrcInt && !isDstInt { // Float to float.
			var tp byte
			if inst == FMOVD {
				tp = 0b01
			}
			a.Buf.Write([]byte{
				(srcRegBits << 5) | dstRegBits,
				0b0_10000_00 | (srcRegBits >> 3),
				tp<<6 | 0b00_1_00000,
				0b000_11110,
			})
		} else if isSrcInt && !isDstInt { // Int to float.
			var tp, sf byte
			if inst == FMOVD {
				tp, sf = 0b01, 0b1
			}
			a.Buf.Write([]byte{
				(srcRegBits << 5) | dstRegBits,
				(srcRegBits >> 3),
				tp<<6 | 0b00_1_00_111,
				sf<<7 | 0b0_00_11110,
			})
		} else { // Float to int.
			var tp, sf byte
			if inst == FMOVD {
				tp, sf = 0b01, 0b1
			}
			a.Buf.Write([]byte{
				(srcRegBits << 5) | dstRegBits,
				(srcRegBits >> 3),
				tp<<6 | 0b00_1_00_110,
				sf<<7 | 0b0_00_11110,
			})
		}

	case MOVD, MOVWU:
		if err = checkRegisterToRegisterType(n.SrcReg, n.DstReg, true, true); err != nil {
			return
		}

		srcRegBits, dstRegBits := registerBits(n.SrcReg), registerBits(n.DstReg)
		if n.SrcReg == REGZERO && inst == MOVD {
			// If this is 64-bit mov from zero register, then we encode this as MOVK.
			// See "Move wide (immediate)" in
			// https://developer.arm.com/documentation/ddi0602/2021-06/Index-by-Encoding/Data-Processing----Immediate
			a.Buf.Write([]byte{
				dstRegBits,
				0x0,
				0b1000_0000,
				0b1_10_10010,
			})
		} else {
			// MOV can be encoded as ORR (shifted register): "ORR Wd, WZR, Wm".
			// https://developer.arm.com/documentation/100069/0609/A64-General-Instructions/MOV--register-

			var sf byte
			if inst == MOVD {
				sf = 0b1
			}
			a.Buf.Write([]byte{
				(zeroRegisterBits << 5) | dstRegBits,
				(zeroRegisterBits >> 3),
				0b000_00000 | srcRegBits,
				sf<<7 | 0b0_01_01010,
			})
		}

	case MRS:
		if n.SrcReg != REG_FPSR {
			return fmt.Errorf("MRS has only support for FPSR register as a src but got %s", RegisterName(n.SrcReg))
		}

		// For how to specify FPSR register, see "Accessing FPSR" in:
		// https://developer.arm.com/documentation/ddi0595/2021-12/AArch64-Registers/FPSR--Floating-point-Status-Register?lang=en
		dstRegBits := registerBits(n.DstReg)
		a.Buf.Write([]byte{
			0b001<<5 | dstRegBits,
			0b0100<<4 | 0b0100,
			0b0011_0000 | 0b11<<3 | 0b011,
			0b1101_0101,
		})

	case MSR:
		if n.DstReg != REG_FPSR {
			return fmt.Errorf("MSR has only support for FPSR register as a dst but got %s", RegisterName(n.SrcReg))
		}

		// For how to specify FPSR register, see "Accessing FPSR" in:
		// https://developer.arm.com/documentation/ddi0595/2021-12/AArch64-Registers/FPSR--Floating-point-Status-Register?lang=en
		srcRegBits := registerBits(n.SrcReg)
		a.Buf.Write([]byte{
			0b001<<5 | srcRegBits,
			0b0100<<4 | 0b0100,
			0b0001_0000 | 0b11<<3 | 0b011,
			0b1101_0101,
		})

	case MUL, MULW:
		// Multiplications are encoded as MADD (zero register, src, dst), dst = zero + (src * dst) = src * dst.
		// See "Data-processing (3 source)" in
		// https://developer.arm.com/documentation/ddi0602/2021-06/Index-by-Encoding/Data-Processing----Register?lang=en
		if err = checkRegisterToRegisterType(n.SrcReg, n.DstReg, true, true); err != nil {
			return
		}

		var sf byte
		if inst == MUL {
			sf = 0b1
		}

		srcRegBits, dstRegBits := registerBits(n.SrcReg), registerBits(n.DstReg)

		a.Buf.Write([]byte{
			dstRegBits<<5 | dstRegBits,
			zeroRegisterBits<<2 | dstRegBits>>3,
			srcRegBits,
			sf<<7 | 0b11011,
		})

	case NEG, NEGW:
		srcRegBits, dstRegBits := registerBits(n.SrcReg), registerBits(n.DstReg)

		if err = checkRegisterToRegisterType(n.SrcReg, n.DstReg, true, true); err != nil {
			return
		}

		// NEG is encded as "SUB dst, XZR, src" = "dst = 0 - src"
		// https://developer.arm.com/documentation/ddi0596/2021-12/Index-by-Encoding/Data-Processing----Register?lang=en#addsub_shift
		var sf byte
		if inst == NEG {
			sf = 0b1
		}

		a.Buf.Write([]byte{
			(zeroRegisterBits << 5) | dstRegBits,
			(zeroRegisterBits >> 3),
			srcRegBits,
			sf<<7 | 0b0_10_00000 | 0b0_00_01011,
		})

	case SDIV, SDIVW, UDIV, UDIVW:
		srcRegBits, dstRegBits := registerBits(n.SrcReg), registerBits(n.DstReg)

		if err = checkRegisterToRegisterType(n.SrcReg, n.DstReg, true, true); err != nil {
			return
		}

		// See "Data-processing (2 source)" in
		// https://developer.arm.com/documentation/ddi0602/2021-06/Index-by-Encoding/Data-Processing----Register?lang=en
		var sf, opcode byte
		switch inst {
		case SDIV:
			sf, opcode = 0b1, 0b000011
		case SDIVW:
			sf, opcode = 0b0, 0b000011
		case UDIV:
			sf, opcode = 0b1, 0b000010
		case UDIVW:
			sf, opcode = 0b0, 0b000010
		}

		a.Buf.Write([]byte{
			(dstRegBits << 5) | dstRegBits,
			opcode<<2 | (dstRegBits >> 3),
			0b110_00000 | srcRegBits,
			sf<<7 | 0b0_00_11010,
		})

	case SCVTFD, SCVTFWD, SCVTFS, SCVTFWS, UCVTFD, UCVTFS, UCVTFWD, UCVTFWS:
		srcRegBits, dstRegBits := registerBits(n.SrcReg), registerBits(n.DstReg)

		if err = checkRegisterToRegisterType(n.SrcReg, n.DstReg, true, false); err != nil {
			return
		}

		// "Conversion between floating-point and integer" in
		// https://developer.arm.com/documentation/ddi0596/2021-12/Index-by-Encoding/Data-Processing----Scalar-Floating-Point-and-Advanced-SIMD?lang=en#floatdp1
		var sf, tp, opcode byte
		switch inst {
		case SCVTFD: // 64-bit integer to double
			sf, tp, opcode = 0b1, 0b01, 0b010
		case SCVTFWD: // 32-bit integer to double
			sf, tp, opcode = 0b0, 0b01, 0b010
		case SCVTFS: // 64-bit integer to single
			sf, tp, opcode = 0b1, 0b00, 0b010
		case SCVTFWS: // 32-bit integer to single
			sf, tp, opcode = 0b0, 0b00, 0b010
		case UCVTFD: // 64-bit to double
			sf, tp, opcode = 0b1, 0b01, 0b011
		case UCVTFWD: // 32-bit to double
			sf, tp, opcode = 0b0, 0b01, 0b011
		case UCVTFS: // 64-bit to single
			sf, tp, opcode = 0b1, 0b00, 0b011
		case UCVTFWS: // 32-bit to single
			sf, tp, opcode = 0b0, 0b00, 0b011
		}

		a.Buf.Write([]byte{
			(srcRegBits << 5) | dstRegBits,
			(srcRegBits >> 3),
			tp<<6 | 0b00_1_00_000 | opcode,
			sf<<7 | 0b0_0_0_11110,
		})

	case SXTB, SXTBW, SXTH, SXTHW, SXTW, UXTW:
		if err = checkRegisterToRegisterType(n.SrcReg, n.DstReg, true, true); err != nil {
			return
		}

		srcRegBits, dstRegBits := registerBits(n.SrcReg), registerBits(n.DstReg)
		if n.SrcReg == REGZERO {
			// If the source is zero register, we encode as MOV dst, zero.
			var sf byte
			if inst == MOVD {
				sf = 0b1
			}
			a.Buf.Write([]byte{
				(zeroRegisterBits << 5) | dstRegBits,
				(zeroRegisterBits >> 3),
				0b000_00000 | srcRegBits,
				sf<<7 | 0b0_01_01010,
			})
			return
		}

		// SXTB is encoded as "SBFM Wd, Wn, #0, #7"
		// https://developer.arm.com/documentation/dui0801/g/A64-General-Instructions/SXTB
		// SXTH is encoded as "SBFM Wd, Wn, #0, #15"
		// https://developer.arm.com/documentation/dui0801/g/A64-General-Instructions/SXTH
		// SXTW is encoded as "SBFM Xd, Xn, #0, #31"
		// https://developer.arm.com/documentation/dui0802/b/A64-General-Instructions/SXTW

		var n, sf, imms, opc byte
		switch inst {
		case SXTB:
			n, sf, imms = 0b1, 0b1, 0x7
		case SXTBW:
			n, sf, imms = 0b0, 0b0, 0x7
		case SXTH:
			n, sf, imms = 0b1, 0b1, 0xf
		case SXTHW:
			n, sf, imms = 0b0, 0b0, 0xf
		case SXTW:
			n, sf, imms = 0b1, 0b1, 0x1f
		}

		a.Buf.Write([]byte{
			(srcRegBits << 5) | dstRegBits,
			imms<<2 | (srcRegBits >> 3),
			n << 6,
			sf<<7 | opc<<5 | 0b10011,
		})
	default:
		return errorEncodingUnsupported(n)
	}
	return
}

func (a *AssemblerImpl) EncodeLeftShiftedRegisterToRegister(n *NodeImpl) (err error) {

	baseRegBits, err := intRegisterBits(n.SrcReg)
	if err != nil {
		return err
	}
	shiftTargetRegBits, err := intRegisterBits(n.SrcReg2)
	if err != nil {
		return err
	}
	dstRegBits, err := intRegisterBits(n.DstReg)
	if err != nil {
		return err
	}

	switch n.Instruction {
	case ADD:
		// https://developer.arm.com/documentation/ddi0596/2021-12/Index-by-Encoding/Data-Processing----Register?lang=en#addsub_shift
		const logicalLeftShiftBits = 0b00
		if n.SrcConst < 0 || n.SrcConst > 64 {
			return fmt.Errorf("shift amount must fit in unsigned 6-bit integer (0-64) but got %d", n.SrcConst)
		}
		shiftByte := byte(n.SrcConst)
		a.Buf.Write([]byte{
			(baseRegBits << 5) | dstRegBits,
			(shiftByte << 2) | (baseRegBits >> 3),
			(logicalLeftShiftBits << 6) | shiftTargetRegBits,
			0b1000_1011,
		})
	default:
		return errorEncodingUnsupported(n)
	}
	return
}

func (a *AssemblerImpl) EncodeTwoRegistersToRegister(n *NodeImpl) (err error) {
	switch inst := n.Instruction; inst {
	case AND, ANDW, ORR, ORRW, EOR, EORW:
		srcRegBits, srcReg2Bits, dstRegBits := registerBits(n.SrcReg), registerBits(n.SrcReg2), registerBits(n.DstReg)
		var sf, opc byte
		switch inst {
		case AND:
			sf, opc = 0b1, 0b00
		case ANDW:
			sf, opc = 0b0, 0b00
		case ORR:
			sf, opc = 0b1, 0b01
		case ORRW:
			sf, opc = 0b0, 0b01
		case EOR:
			sf, opc = 0b1, 0b10
		case EORW:
			sf, opc = 0b0, 0b10
		}
		a.Buf.Write([]byte{
			(srcReg2Bits << 5) | dstRegBits,
			(srcReg2Bits >> 3),
			srcRegBits,
			sf<<7 | opc<<5 | 0b01010,
		})
	case ASR, ASRW, LSL, LSLW, LSR, LSRW, ROR, RORW:
		srcRegBits, srcReg2Bits, dstRegBits := registerBits(n.SrcReg), registerBits(n.SrcReg2), registerBits(n.DstReg)

		var sf, opcode byte
		switch inst {
		case ASR:
			sf, opcode = 0b1, 0b001010
		case ASRW:
			sf, opcode = 0b0, 0b001010
		case LSL:
			sf, opcode = 0b1, 0b001000
		case LSLW:
			sf, opcode = 0b0, 0b001000
		case LSR:
			sf, opcode = 0b1, 0b001001
		case LSRW:
			sf, opcode = 0b0, 0b001001
		case ROR:
			sf, opcode = 0b1, 0b001011
		case RORW:
			sf, opcode = 0b0, 0b001011
		}
		a.Buf.Write([]byte{
			(srcReg2Bits << 5) | dstRegBits,
			opcode<<2 | (srcReg2Bits >> 3),
			0b110_00000 | srcRegBits,
			sf<<7 | 0b0_00_11010,
		})

	case SDIV, SDIVW, UDIV, UDIVW:
		srcRegBits, srcReg2Bits, dstRegBits := registerBits(n.SrcReg), registerBits(n.SrcReg2), registerBits(n.DstReg)

		// See "Data-processing (2 source)" in
		// https://developer.arm.com/documentation/ddi0602/2021-06/Index-by-Encoding/Data-Processing----Register?lang=en
		var sf, opcode byte
		switch inst {
		case SDIV:
			sf, opcode = 0b1, 0b000011
		case SDIVW:
			sf, opcode = 0b0, 0b000011
		case UDIV:
			sf, opcode = 0b1, 0b000010
		case UDIVW:
			sf, opcode = 0b0, 0b000010
		}

		a.Buf.Write([]byte{
			(srcReg2Bits << 5) | dstRegBits,
			opcode<<2 | (srcReg2Bits >> 3),
			0b110_00000 | srcRegBits,
			sf<<7 | 0b0_00_11010,
		})
	case SUB, SUBW:
		srcRegBits, srcReg2Bits, dstRegBits := registerBits(n.SrcReg), registerBits(n.SrcReg2), registerBits(n.DstReg)

		var sf byte
		if inst == SUB {
			sf = 0b1
		}

		a.Buf.Write([]byte{
			(srcReg2Bits << 5) | dstRegBits,
			(srcReg2Bits >> 3),
			srcRegBits,
			sf<<7 | 0b0_10_01011,
		})

	case FSUBD, FSUBS:
		srcRegBits, srcReg2Bits, dstRegBits := registerBits(n.SrcReg), registerBits(n.SrcReg2), registerBits(n.DstReg)
		var tp byte
		if inst == FSUBD {
			tp = 0b01
		}
		a.Buf.Write([]byte{
			(srcReg2Bits << 5) | dstRegBits,
			0b0011_10_00 | (srcReg2Bits >> 3),
			tp<<6 | 0b00_1_00000 | srcRegBits,
			0b0_00_11110,
		})
	default:
		return errorEncodingUnsupported(n)
	}
	return
}

func (a *AssemblerImpl) EncodeThreeRegistersToRegister(n *NodeImpl) (err error) {
	switch n.Instruction {
	case MSUB, MSUBW:
		// Dst = Src2 - (Src1 * Src3)
		// "Data-processing (3 source)" in:
		// https://developer.arm.com/documentation/ddi0596/2021-12/Index-by-Encoding/Data-Processing----Register?lang=en
		src1RegBits, err := intRegisterBits(n.SrcReg)
		if err != nil {
			return err
		}
		src2RegBits, err := intRegisterBits(n.SrcReg2)
		if err != nil {
			return err
		}
		src3RegBits, err := intRegisterBits(n.DstReg)
		if err != nil {
			return err
		}
		dstRegBits, err := intRegisterBits(n.DstReg2)
		if err != nil {
			return err
		}

		var sf byte // is zero for MSUBW (32-bit MSUB).
		if n.Instruction == MSUB {
			sf = 0b1
		}

		a.Buf.Write([]byte{
			(src3RegBits << 5) | dstRegBits,
			0b1_0000000 | (src2RegBits << 2) | (src3RegBits >> 3),
			src1RegBits,
			sf<<7 | 0b00_11011,
		})
	default:
		return errorEncodingUnsupported(n)
	}
	return
}

func (a *AssemblerImpl) EncodeTwoRegistersToNone(n *NodeImpl) (err error) {
	switch n.Instruction {
	case CMPW, CMP:
		// Comare on two registesr is an alias for "SUBS (src1, src2) ZERO"
		// which can be encoded as SUBS (shifted registers) with zero shifting.
		// https://developer.arm.com/documentation/ddi0596/2021-12/Index-by-Encoding/Data-Processing----Register?lang=en#addsub_shift
		src1RegBits, err := intRegisterBits(n.SrcReg)
		if err != nil {
			return err
		}
		src2RegBits, err := intRegisterBits(n.SrcReg2)
		if err != nil {
			return err
		}

		var op byte
		if n.Instruction == CMP {
			op = 0b111
		} else {
			op = 0b011
		}

		a.Buf.Write([]byte{
			(src2RegBits << 5) | zeroRegisterBits,
			(src2RegBits >> 3),
			src1RegBits,
			0b01011 | (op << 5),
		})
	case FCMPS, FCMPD:
		// "Floating-point compare" section in:
		// https://developer.arm.com/documentation/ddi0596/2021-12/Index-by-Encoding/Data-Processing----Scalar-Floating-Point-and-Advanced-SIMD?lang=en
		src1RegBits, err := floatRegisterBits(n.SrcReg)
		if err != nil {
			return err
		}
		src2RegBits, err := floatRegisterBits(n.SrcReg2)
		if err != nil {
			return err
		}

		var ftype byte // is zero for FCMPS (single precision float compare).
		if n.Instruction == FCMPD {
			ftype = 0b01
		}
		a.Buf.Write([]byte{
			(src2RegBits << 5) | 0b00000,
			0b001000_00 | (src2RegBits >> 3),
			ftype<<6 | 0b1_00000 | src1RegBits,
			0b000_11110,
		})
	default:
		return errorEncodingUnsupported(n)
	}
	return
}

func (a *AssemblerImpl) EncodeRegisterAndConstToNone(n *NodeImpl) (err error) {
	// https://developer.arm.com/documentation/ddi0596/2021-12/Base-Instructions/CMP--immediate---Compare--immediate---an-alias-of-SUBS--immediate--?lang=en
	if n.SrcConst < 0 || n.SrcConst > 4095 {
		return fmt.Errorf("immediate for CMP must fit in 0 to 4095 but got %d", n.SrcConst)
	} else if n.SrcReg == REGZERO {
		return errors.New("ZERO register is not supported for CMP (immediate)")
	}

	srcRegBits, err := intRegisterBits(n.SrcReg)
	if err != nil {
		return err
	}

	a.Buf.Write([]byte{
		(srcRegBits << 5) | zeroRegisterBits,
		(byte(n.SrcConst) << 2) | (srcRegBits >> 3),
		byte(n.SrcConst >> 6),
		0b111_10001,
	})
	return
}

// encodeRegisterToMemory:  FMOVD REG_FLOAT, [REG_INT + IMMEDIATE]
// encodeRegisterToMemory:  FMOVD REG_FLOAT, [REG_INT + REG_INT]
// encodeRegisterToMemory:  FMOVS REG_FLOAT, [REG_INT + IMMEDIATE]
// encodeRegisterToMemory:  FMOVS REG_FLOAT, [REG_INT + REG_INT]
// encodeRegisterToMemory:  MOVB REG_INT, [REG_INT + REG_INT]
// encodeRegisterToMemory:  MOVB ZERO, [REG_INT + REG_INT]
// encodeRegisterToMemory:  MOVD REG_INT, [REG_INT + IMMEDIATE]
// encodeRegisterToMemory:  MOVD REG_INT, [REG_INT + REG_INT]
// encodeRegisterToMemory:  MOVD ZERO, [REG_INT + IMMEDIATE]
// encodeRegisterToMemory:  MOVD ZERO, [REG_INT + REG_INT]
// encodeRegisterToMemory:  MOVH REG_INT, [REG_INT + REG_INT]
// encodeRegisterToMemory:  MOVH ZERO, [REG_INT + REG_INT]
// encodeRegisterToMemory:  MOVW REG_INT, [REG_INT + IMMEDIATE]
// encodeRegisterToMemory:  MOVW REG_INT, [REG_INT + REG_INT]
// encodeRegisterToMemory:  MOVW ZERO, [REG_INT + IMMEDIATE]
// encodeRegisterToMemory:  MOVW ZERO, [REG_INT + REG_INT]
// encodeRegisterToMemory:  MOVWU REG_INT, [REG_INT + IMMEDIATE]
func (a *AssemblerImpl) EncodeRegisterToMemory(n *NodeImpl) (err error) {
	return
}

// encodeMemoryToRegister:  ADR [nil + IMMEDIATE], REG_INT
// encodeMemoryToRegister:  FMOVD [REG_INT + IMMEDIATE], REG_FLOAT
// encodeMemoryToRegister:  FMOVD [REG_INT + REG_INT], REG_FLOAT
// encodeMemoryToRegister:  FMOVS [REG_INT + IMMEDIATE], REG_FLOAT
// encodeMemoryToRegister:  FMOVS [REG_INT + REG_INT], REG_FLOAT
// encodeMemoryToRegister:  MOVB [REG_INT + REG_INT], REG_INT
// encodeMemoryToRegister:  MOVBU [REG_INT + REG_INT], REG_INT
// encodeMemoryToRegister:  MOVD [REG_INT + IMMEDIATE], REG_INT
// encodeMemoryToRegister:  MOVD [REG_INT + REG_INT], REG_INT
// encodeMemoryToRegister:  MOVH [REG_INT + REG_INT], REG_INT
// encodeMemoryToRegister:  MOVHU [REG_INT + REG_INT], REG_INT
// encodeMemoryToRegister:  MOVW [REG_INT + IMMEDIATE], REG_INT
// encodeMemoryToRegister:  MOVW [REG_INT + REG_INT], REG_INT
// encodeMemoryToRegister:  MOVWU [REG_INT + IMMEDIATE], REG_INT
// encodeMemoryToRegister:  MOVWU [REG_INT + REG_INT], REG_INT
func (a *AssemblerImpl) EncodeMemoryToRegister(n *NodeImpl) (err error) {
	return
}

// encodeConstToRegister:  ADD IMMEDIATE, REG_INT
// encodeConstToRegister:  LSR IMMEDIATE, REG_INT
// encodeConstToRegister:  MOVD IMMEDIATE, REG_INT
// encodeConstToRegister:  MOVW IMMEDIATE, REG_INT
// encodeConstToRegister:  SUB IMMEDIATE, REG_INT
// encodeConstToRegister:  SUBS IMMEDIATE, REG_INT
func (a *AssemblerImpl) EncodeConstToRegister(n *NodeImpl) (err error) {
	return
}

// encodeSIMDByteToSIMDByte:  VCNT REG_FLOAT.B8, REG_FLOAT.B8
func (a *AssemblerImpl) EncodeSIMDByteToSIMDByte(n *NodeImpl) (err error) {
	return
}

// encodeSIMDByteToRegister:  VUADDLV REG_FLOAT.B8, REG_FLOAT
// encodeSIMDByteToSIMDByte:  VCNT REG_FLOAT.B8, REG_FLOAT.B8
func (a *AssemblerImpl) EncodeSIMDByteToRegister(n *NodeImpl) (err error) {
	return
}

// encodeTwoSIMDBytesToSIMDByteRegister: VBIT (REG_FLOAT.B8, REG_FLOAT.B8), REG_FLOAT.B8
func (a *AssemblerImpl) EncodeTwoSIMDBytesToSIMDByteRegister(n *NodeImpl) (err error) {
	return
}

var zeroRegisterBits byte = 0b11111

func isIntRegister(r asm.Register) bool {
	return REG_R0 <= r && r <= REGZERO
}

func isFloatRegister(r asm.Register) bool {
	return REG_F0 <= r && r <= REG_F31
}

func isConditionalRegister(r asm.Register) bool {
	return REG_COND_EQ <= r && r <= REG_COND_NV
}

func intRegisterBits(r asm.Register) (ret byte, err error) {
	if !isIntRegister(r) {
		err = fmt.Errorf("%s is not integer", RegisterName(r))
	} else {
		ret = byte((r - REG_R0))
	}
	return
}

func floatRegisterBits(r asm.Register) (ret byte, err error) {
	if !isFloatRegister(r) {
		err = fmt.Errorf("%s is not float", RegisterName(r))
	} else {
		ret = byte((r - REG_F0))
	}
	return
}

func registerBits(r asm.Register) (ret byte) {
	if isIntRegister(r) {
		ret = byte((r - REG_R0))
	} else {
		ret = byte((r - REG_F0))
	}
	return
}
