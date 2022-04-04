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
	srcRegBits, dstRegBits := registerBits(n.SrcReg), registerBits(n.DstReg)

	switch inst := n.Instruction; inst {
	case ADD, ADDW, SUB:
		if err = checkRegisterToRegisterType(n.SrcReg, n.DstReg, true, true); err != nil {
			return
		}

		if n.SrcConst < 0 || n.SrcConst > 64 {
			return fmt.Errorf("shift amount must fit in unsigned 6-bit integer (0-64) but got %d", n.SrcConst)
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

		a.Buf.Write([]byte{
			(dstRegBits << 5) | dstRegBits,
			(dstRegBits >> 3),
			srcRegBits,
			(sfops << 5) | 0b01011,
		})

		// CLZ REG_INT, REG_INT
		// CLZW REG_INT, REG_INT
		// CSET COND_EQ, REG_INT
		// CSET COND_GE, REG_INT
		// CSET COND_GT, REG_INT
		// CSET COND_HI, REG_INT
		// CSET COND_HS, REG_INT
		// CSET COND_LE, REG_INT
		// CSET COND_LO, REG_INT
		// CSET COND_LS, REG_INT
		// CSET COND_LT, REG_INT
		// CSET COND_MI, REG_INT
		// CSET COND_NE, REG_INT
		// FABSD REG_FLOAT, REG_FLOAT
		// FABSS REG_FLOAT, REG_FLOAT
		// FADDD REG_FLOAT, REG_FLOAT
		// FADDS REG_FLOAT, REG_FLOAT
		// FCVTDS REG_FLOAT, REG_FLOAT
		// FCVTSD REG_FLOAT, REG_FLOAT
		// FCVTZSD REG_FLOAT, REG_INT
		// FCVTZSDW REG_FLOAT, REG_INT
		// FCVTZSS REG_FLOAT, REG_INT
		// FCVTZSSW REG_FLOAT, REG_INT
		// FCVTZUD REG_FLOAT, REG_INT
		// FCVTZUDW REG_FLOAT, REG_INT
		// FCVTZUS REG_FLOAT, REG_INT
		// FCVTZUSW REG_FLOAT, REG_INT
		// FDIVD REG_FLOAT, REG_FLOAT
		// FDIVS REG_FLOAT, REG_FLOAT
		// FMAXD REG_FLOAT, REG_FLOAT
		// FMAXS REG_FLOAT, REG_FLOAT
		// FMIND REG_FLOAT, REG_FLOAT
		// FMINS REG_FLOAT, REG_FLOAT
		// FMOVD REG_FLOAT, REG_FLOAT
		// FMOVD REG_FLOAT, REG_INT
		// FMOVD REG_INT, REG_FLOAT
		// FMOVD ZERO, REG_FLOAT
		// FMOVS REG_FLOAT, REG_INT
		// FMOVS REG_INT, REG_FLOAT
		// FMOVS ZERO, REG_FLOAT
		// FMULD REG_FLOAT, REG_FLOAT
		// FMULS REG_FLOAT, REG_FLOAT
		// FNEGD REG_FLOAT, REG_FLOAT
		// FNEGS REG_FLOAT, REG_FLOAT
		// FRINTMD REG_FLOAT, REG_FLOAT
		// FRINTMS REG_FLOAT, REG_FLOAT
		// FRINTND REG_FLOAT, REG_FLOAT
		// FRINTNS REG_FLOAT, REG_FLOAT
		// FRINTPD REG_FLOAT, REG_FLOAT
		// FRINTPS REG_FLOAT, REG_FLOAT
		// FRINTZD REG_FLOAT, REG_FLOAT
		// FRINTZS REG_FLOAT, REG_FLOAT
		// FSQRTD REG_FLOAT, REG_FLOAT
		// FSQRTS REG_FLOAT, REG_FLOAT
		// MOVD REG_INT, REG_INT
		// MOVD ZERO, REG_INT
		// MOVW REG_INT, REG_INT
		// MRS FPSR, REG_INT
		// MSR ZERO, FPSR
		// MUL REG_INT, REG_INT
		// MULW REG_INT, REG_INT
		// NEG REG_INT, REG_INT
		// NEGW REG_INT, REG_INT
		// RBIT REG_INT, REG_INT
		// RBITW REG_INT, REG_INT
		// SCVTFD REG_INT, REG_FLOAT
		// SCVTFD ZERO, REG_FLOAT
		// SCVTFS REG_INT, REG_FLOAT
		// SCVTFS ZERO, REG_FLOAT
		// SCVTFWD REG_INT, REG_FLOAT
		// SCVTFWD ZERO, REG_FLOAT
		// SCVTFWS REG_INT, REG_FLOAT
		// SCVTFWS ZERO, REG_FLOAT
		// SDIV REG_INT, REG_INT
		// SDIV REG_INT, ZERO
		// SDIVW REG_INT, REG_INT
		// SDIVW REG_INT, ZERO
		// SXTB REG_INT, REG_INT
		// SXTB ZERO, ZERO
		// SXTBW REG_INT, REG_INT
		// SXTBW ZERO, ZERO
		// SXTH REG_INT, REG_INT
		// SXTH ZERO, ZERO
		// SXTHW REG_INT, REG_INT
		// SXTHW ZERO, ZERO
		// SXTW REG_INT, REG_INT
		// SXTW ZERO, ZERO
		// UCVTFD REG_INT, REG_FLOAT
		// UCVTFD ZERO, REG_FLOAT
		// UCVTFS REG_INT, REG_FLOAT
		// UCVTFS ZERO, REG_FLOAT
		// UCVTFWD REG_INT, REG_FLOAT
		// UCVTFWD ZERO, REG_FLOAT
		// UCVTFWS REG_INT, REG_FLOAT
		// UCVTFWS ZERO, REG_FLOAT
		// UDIV REG_INT, REG_INT
		// UDIV REG_INT, ZERO
		// UDIVW REG_INT, REG_INT
		// UXTW REG_INT, REG_INT
		// UXTW ZERO, ZERO
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

// encodeTwoRegistersToRegister:  AND (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  ANDW (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  ASR (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  ASRW (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  EOR (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  EOR (REG_INT, ZERO), REG_INT
// encodeTwoRegistersToRegister:  EOR (ZERO, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  EOR (ZERO, ZERO), ZERO
// encodeTwoRegistersToRegister:  EORW (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  EORW (REG_INT, ZERO), REG_INT
// encodeTwoRegistersToRegister:  EORW (ZERO, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  EORW (ZERO, ZERO), ZERO
// encodeTwoRegistersToRegister:  FSUBD (REG_FLOAT, REG_FLOAT), REG_FLOAT
// encodeTwoRegistersToRegister:  FSUBS (REG_FLOAT, REG_FLOAT), REG_FLOAT
// encodeTwoRegistersToRegister:  LSL (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  LSLW (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  LSR (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  LSRW (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  ORR (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  ORRW (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  ROR (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  RORW (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  SDIV (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  SDIV (REG_INT, ZERO), REG_INT
// encodeTwoRegistersToRegister:  SDIVW (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  SDIVW (REG_INT, ZERO), REG_INT
// encodeTwoRegistersToRegister:  SUB (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  SUB (REG_INT, ZERO), REG_INT
// encodeTwoRegistersToRegister:  SUB (ZERO, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  SUBW (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  SUBW (REG_INT, ZERO), REG_INT
// encodeTwoRegistersToRegister:  SUBW (ZERO, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  UDIV (REG_INT, REG_INT), REG_INT
// encodeTwoRegistersToRegister:  UDIV (REG_INT, ZERO), REG_INT
// encodeTwoRegistersToRegister:  UDIVW (REG_INT, REG_INT), REG_INT
func (a *AssemblerImpl) EncodeTwoRegistersToRegister(n *NodeImpl) (err error) {
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

// encodeRegisterAndConstToNone:  CMP (REG_INT, IMMEDIATE)
func (a *AssemblerImpl) EncodeRegisterAndConstToNone(n *NodeImpl) (err error) {
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

const zeroRegisterBits byte = 0b11111

func isIntRegister(r asm.Register) bool {
	return REG_R0 <= r && r <= REGZERO
}

func isFloatRegister(r asm.Register) bool {
	return REG_F0 <= r && r <= REG_F31
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
