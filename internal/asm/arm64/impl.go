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
	case OperandTypesNoneToRegister:
		err = a.EncodeNoneToRegister(n)
	case OperandTypesNoneToMemory:
		err = a.EncodeNoneToMemory(n)
	case OperandTypesNoneToBranch:
		err = a.EncodeNoneToBranch(n)
	case OperandTypesRegisterToRegister:
		err = a.EncodeRegisterToRegister(n)
	case OperandTypesLeftShiftedRegisterToRegister:
		err = a.EncodeLeftShiftedRegisterToRegister(n)
	case OperandTypesTwoRegistersToRegister:
		err = a.EncodeTwoRegistersToRegister(n)
	case OperandTypesTwoRegisters:
		err = a.EncodeTwoRegisters(n)
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

func errorEncodingUnsupported(n *NodeImpl) error {
	return fmt.Errorf("%s is unsupported for %s type", InstructionName(n.Instruction), n.Types)
}

func (a *AssemblerImpl) EncodeNoneToNone(n *NodeImpl) (err error) {
	if n.Instruction != NOP {
		err = errorEncodingUnsupported(n)
	}
	return
}

func (a *AssemblerImpl) EncodeNoneToRegister(n *NodeImpl) (err error) {
	if n.Instruction != RET {
		return errorEncodingUnsupported(n)
	}

	if !isIntRegister(n.DstReg) {
		return fmt.Errorf("RET needs integer register as desination but got %s", RegisterName(n.DstReg))
	}

	regBits := intRegisterBits(n.DstReg)
	a.Buf.Write([]byte{
		0x00 | (regBits << 5),
		0x00 | (regBits >> 3),
		0b01011111,
		0b11010110,
	})
	return
}

// encodeNoneToMemory:  B [REG_INT + IMMEDIATE]
func (a *AssemblerImpl) EncodeNoneToMemory(n *NodeImpl) (err error) {
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

// encodeRegisterToRegister:  ADD REG_INT, REG_INT
// encodeRegisterToRegister:  ADDW REG_INT, REG_INT
// encodeRegisterToRegister:  CLZ REG_INT, REG_INT
// encodeRegisterToRegister:  CLZW REG_INT, REG_INT
// encodeRegisterToRegister:  CSET COND_EQ, REG_INT
// encodeRegisterToRegister:  CSET COND_GE, REG_INT
// encodeRegisterToRegister:  CSET COND_GT, REG_INT
// encodeRegisterToRegister:  CSET COND_HI, REG_INT
// encodeRegisterToRegister:  CSET COND_HS, REG_INT
// encodeRegisterToRegister:  CSET COND_LE, REG_INT
// encodeRegisterToRegister:  CSET COND_LO, REG_INT
// encodeRegisterToRegister:  CSET COND_LS, REG_INT
// encodeRegisterToRegister:  CSET COND_LT, REG_INT
// encodeRegisterToRegister:  CSET COND_MI, REG_INT
// encodeRegisterToRegister:  CSET COND_NE, REG_INT
// encodeRegisterToRegister:  FABSD REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FABSS REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FADDD REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FADDS REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FCVTDS REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FCVTSD REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FCVTZSD REG_FLOAT, REG_INT
// encodeRegisterToRegister:  FCVTZSDW REG_FLOAT, REG_INT
// encodeRegisterToRegister:  FCVTZSS REG_FLOAT, REG_INT
// encodeRegisterToRegister:  FCVTZSSW REG_FLOAT, REG_INT
// encodeRegisterToRegister:  FCVTZUD REG_FLOAT, REG_INT
// encodeRegisterToRegister:  FCVTZUDW REG_FLOAT, REG_INT
// encodeRegisterToRegister:  FCVTZUS REG_FLOAT, REG_INT
// encodeRegisterToRegister:  FCVTZUSW REG_FLOAT, REG_INT
// encodeRegisterToRegister:  FDIVD REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FDIVS REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FMAXD REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FMAXS REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FMIND REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FMINS REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FMOVD REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FMOVD REG_FLOAT, REG_INT
// encodeRegisterToRegister:  FMOVD REG_INT, REG_FLOAT
// encodeRegisterToRegister:  FMOVD ZERO, REG_FLOAT
// encodeRegisterToRegister:  FMOVS REG_FLOAT, REG_INT
// encodeRegisterToRegister:  FMOVS REG_INT, REG_FLOAT
// encodeRegisterToRegister:  FMOVS ZERO, REG_FLOAT
// encodeRegisterToRegister:  FMULD REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FMULS REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FNEGD REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FNEGS REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FRINTMD REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FRINTMS REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FRINTND REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FRINTNS REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FRINTPD REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FRINTPS REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FRINTZD REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FRINTZS REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FSQRTD REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  FSQRTS REG_FLOAT, REG_FLOAT
// encodeRegisterToRegister:  MOVD REG_INT, REG_INT
// encodeRegisterToRegister:  MOVD ZERO, REG_INT
// encodeRegisterToRegister:  MOVW REG_INT, REG_INT
// encodeRegisterToRegister:  MRS FPSR, REG_INT
// encodeRegisterToRegister:  MSR ZERO, FPSR
// encodeRegisterToRegister:  MUL REG_INT, REG_INT
// encodeRegisterToRegister:  MULW REG_INT, REG_INT
// encodeRegisterToRegister:  NEG REG_INT, REG_INT
// encodeRegisterToRegister:  NEGW REG_INT, REG_INT
// encodeRegisterToRegister:  RBIT REG_INT, REG_INT
// encodeRegisterToRegister:  RBITW REG_INT, REG_INT
// encodeRegisterToRegister:  SCVTFD REG_INT, REG_FLOAT
// encodeRegisterToRegister:  SCVTFD ZERO, REG_FLOAT
// encodeRegisterToRegister:  SCVTFS REG_INT, REG_FLOAT
// encodeRegisterToRegister:  SCVTFS ZERO, REG_FLOAT
// encodeRegisterToRegister:  SCVTFWD REG_INT, REG_FLOAT
// encodeRegisterToRegister:  SCVTFWD ZERO, REG_FLOAT
// encodeRegisterToRegister:  SCVTFWS REG_INT, REG_FLOAT
// encodeRegisterToRegister:  SCVTFWS ZERO, REG_FLOAT
// encodeRegisterToRegister:  SDIV REG_INT, REG_INT
// encodeRegisterToRegister:  SDIV REG_INT, ZERO
// encodeRegisterToRegister:  SDIVW REG_INT, REG_INT
// encodeRegisterToRegister:  SDIVW REG_INT, ZERO
// encodeRegisterToRegister:  SUB REG_INT, REG_INT
// encodeRegisterToRegister:  SXTB REG_INT, REG_INT
// encodeRegisterToRegister:  SXTB ZERO, ZERO
// encodeRegisterToRegister:  SXTBW REG_INT, REG_INT
// encodeRegisterToRegister:  SXTBW ZERO, ZERO
// encodeRegisterToRegister:  SXTH REG_INT, REG_INT
// encodeRegisterToRegister:  SXTH ZERO, ZERO
// encodeRegisterToRegister:  SXTHW REG_INT, REG_INT
// encodeRegisterToRegister:  SXTHW ZERO, ZERO
// encodeRegisterToRegister:  SXTW REG_INT, REG_INT
// encodeRegisterToRegister:  SXTW ZERO, ZERO
// encodeRegisterToRegister:  UCVTFD REG_INT, REG_FLOAT
// encodeRegisterToRegister:  UCVTFD ZERO, REG_FLOAT
// encodeRegisterToRegister:  UCVTFS REG_INT, REG_FLOAT
// encodeRegisterToRegister:  UCVTFS ZERO, REG_FLOAT
// encodeRegisterToRegister:  UCVTFWD REG_INT, REG_FLOAT
// encodeRegisterToRegister:  UCVTFWD ZERO, REG_FLOAT
// encodeRegisterToRegister:  UCVTFWS REG_INT, REG_FLOAT
// encodeRegisterToRegister:  UCVTFWS ZERO, REG_FLOAT
// encodeRegisterToRegister:  UDIV REG_INT, REG_INT
// encodeRegisterToRegister:  UDIV REG_INT, ZERO
// encodeRegisterToRegister:  UDIVW REG_INT, REG_INT
// encodeRegisterToRegister:  UXTW REG_INT, REG_INT
// encodeRegisterToRegister:  UXTW ZERO, ZERO
func (a *AssemblerImpl) EncodeRegisterToRegister(n *NodeImpl) (err error) {
	return
}

// encodeLeftShiftedRegisterToRegister:  ADD (REG_INT, REG_INT << 2), REG_INT
// encodeLeftShiftedRegisterToRegister:  ADD (REG_INT, REG_INT << 3), REG_INT
// encodeLeftShiftedRegisterToRegister:  ADD (REG_INT, REG_INT << 4), REG_INT
// encodeLeftShiftedRegisterToRegister:  ADD (REG_INT, REG_INT << 5), REG_INT
func (a *AssemblerImpl) EncodeLeftShiftedRegisterToRegister(n *NodeImpl) (err error) {
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

// encodeTwoRegisters:  MSUB (REG_INT, REG_INT), (REG_INT, REG_INT)
// encodeTwoRegisters:  MSUB (REG_INT, ZERO), (REG_INT, REG_INT)
// encodeTwoRegisters:  MSUBW (REG_INT, REG_INT), (REG_INT, REG_INT)
// encodeTwoRegisters:  MSUBW (REG_INT, ZERO), (REG_INT, REG_INT)
func (a *AssemblerImpl) EncodeTwoRegisters(n *NodeImpl) (err error) {
	return
}

// encodeTwoRegistersToNone:  CMP (REG_INT, REG_INT)
// encodeTwoRegistersToNone:  CMP (REG_INT, ZERO)
// encodeTwoRegistersToNone:  CMP (ZERO, REG_INT)
// encodeTwoRegistersToNone:  CMP (ZERO, ZERO)
// encodeTwoRegistersToNone:  CMPW (REG_INT, REG_INT)
// encodeTwoRegistersToNone:  CMPW (REG_INT, ZERO)
// encodeTwoRegistersToNone:  CMPW (ZERO, REG_INT)
// encodeTwoRegistersToNone:  CMPW (ZERO, ZERO)
// encodeTwoRegistersToNone:  FCMPD (REG_FLOAT, REG_FLOAT)
// encodeTwoRegistersToNone:  FCMPS (REG_FLOAT, REG_FLOAT)
func (a *AssemblerImpl) EncodeTwoRegistersToNone(n *NodeImpl) (err error) {
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

func isIntRegister(r asm.Register) bool {
	return REG_R0 <= r && r <= REG_R30
}

func intRegisterBits(r asm.Register) byte {
	return byte((r - REG_R0))
}
