package arm64debug

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/tetratelabs/wazero/internal/asm"
	asm_arm64 "github.com/tetratelabs/wazero/internal/asm/arm64"
)

func newGoasmAssembler(t *testing.T, tmpReg asm.Register) asm_arm64.Assembler {
	a, err := newAssembler(asm.NilRegister)
	require.NoError(t, err)
	a.CompileStandAlone(asm_arm64.NOP)
	return a
}

func TestAssemblerImpl_encodeNoneToNone(t *testing.T) {
	t.Run("error", func(t *testing.T) {
		a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
		err := a.EncodeNoneToNone(&asm_arm64.NodeImpl{Instruction: asm_arm64.ADD})
		require.EqualError(t, err, "ADD is unsupported for from:none,to:none type")
	})
	t.Run("ok", func(t *testing.T) {
		a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
		err := a.EncodeNoneToNone(&asm_arm64.NodeImpl{Instruction: asm_arm64.NOP})
		require.NoError(t, err)

		// NOP must be ignored.
		actual := a.Buf.Bytes()
		require.Len(t, actual, 0)
	})
}

var intRegisters = []asm.Register{
	asm_arm64.REG_R0, asm_arm64.REG_R1, asm_arm64.REG_R2, asm_arm64.REG_R3, asm_arm64.REG_R4, asm_arm64.REG_R5, asm_arm64.REG_R6,
	asm_arm64.REG_R7, asm_arm64.REG_R8, asm_arm64.REG_R9, asm_arm64.REG_R10, asm_arm64.REG_R11, asm_arm64.REG_R12, asm_arm64.REG_R13,
	asm_arm64.REG_R14, asm_arm64.REG_R15, asm_arm64.REG_R16, asm_arm64.REG_R17, asm_arm64.REG_R18, asm_arm64.REG_R19, asm_arm64.REG_R20,
	asm_arm64.REG_R21, asm_arm64.REG_R22, asm_arm64.REG_R23, asm_arm64.REG_R24, asm_arm64.REG_R25, asm_arm64.REG_R26, asm_arm64.REG_R27,
	asm_arm64.REG_R28, asm_arm64.REG_R29, asm_arm64.REG_R30,
}

func TestAssemblerImpl_EncodeJumpToRegister(t *testing.T) {
	t.Run("error", func(t *testing.T) {
		for _, tc := range []struct {
			n      *asm_arm64.NodeImpl
			expErr string
		}{
			{
				n:      &asm_arm64.NodeImpl{Instruction: asm_arm64.ADD, Types: asm_arm64.OperandTypesNoneToRegister},
				expErr: "ADD is unsupported for from:none,to:register type",
			},
			{
				n:      &asm_arm64.NodeImpl{Instruction: asm_arm64.RET, DstReg: asm.NilRegister},
				expErr: "invalid destination register: nil is not integer",
			},
			{
				n:      &asm_arm64.NodeImpl{Instruction: asm_arm64.RET, DstReg: asm_arm64.REG_F0},
				expErr: "invalid destination register: F0 is not integer",
			},
		} {
			a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
			err := a.EncodeJumpToRegister(tc.n)
			require.EqualError(t, err, tc.expErr)
		}
	})

	t.Run("ok", func(t *testing.T) {
		for _, inst := range []asm.Instruction{
			asm_arm64.B,
			asm_arm64.RET,
		} {
			t.Run(asm_arm64.InstructionName(inst), func(t *testing.T) {
				for _, r := range intRegisters {
					t.Run(asm_arm64.RegisterName(r), func(t *testing.T) {
						// TODO: remove golang-asm dependency in tests.
						goasm := newGoasmAssembler(t, asm.NilRegister)
						if inst == asm_arm64.RET {
							goasm.CompileJumpToRegister(inst, r)
						} else {
							goasm.CompileJumpToMemory(inst, r)
						}

						expected, err := goasm.Assemble()
						require.NoError(t, err)

						a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
						err = a.EncodeJumpToRegister(&asm_arm64.NodeImpl{Instruction: inst, DstReg: r})
						require.NoError(t, err)

						actual := a.Bytes()
						require.Equal(t, expected, actual)
					})
				}
			})
		}
	})
}

func TestAssemblerImpl_EncodeLeftShiftedRegisterToRegister(t *testing.T) {
	t.Run("error", func(t *testing.T) {
		for _, tc := range []struct {
			n      *asm_arm64.NodeImpl
			expErr string
		}{
			{
				n: &asm_arm64.NodeImpl{Instruction: asm_arm64.SUB, Types: asm_arm64.OperandTypesLeftShiftedRegisterToRegister,
					SrcReg: asm_arm64.REG_R0, SrcReg2: asm_arm64.REG_R0, DstReg: asm_arm64.REG_R0},
				expErr: "SUB is unsupported for from:left-shifted-register,to:register type",
			},
			{
				n: &asm_arm64.NodeImpl{Instruction: asm_arm64.ADD,
					SrcConst: -1, SrcReg: asm_arm64.REG_R0, SrcReg2: asm_arm64.REG_R0, DstReg: asm_arm64.REG_R0},
				expErr: "shift amount must fit in unsigned 6-bit integer (0-64) but got -1",
			},
			{
				n: &asm_arm64.NodeImpl{Instruction: asm_arm64.ADD,
					SrcConst: -1, SrcReg: asm_arm64.REG_F0, SrcReg2: asm_arm64.REG_R0, DstReg: asm_arm64.REG_R0},
				expErr: "F0 is not integer",
			},
			{
				n: &asm_arm64.NodeImpl{Instruction: asm_arm64.ADD,
					SrcConst: -1, SrcReg: asm_arm64.REG_R0, SrcReg2: asm_arm64.REG_F0, DstReg: asm_arm64.REG_R0},
				expErr: "F0 is not integer",
			},
			{
				n: &asm_arm64.NodeImpl{Instruction: asm_arm64.ADD,
					SrcConst: -1, SrcReg: asm_arm64.REG_R0, SrcReg2: asm_arm64.REG_R0, DstReg: asm_arm64.REG_F0},
				expErr: "F0 is not integer",
			},
		} {
			a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
			err := a.EncodeLeftShiftedRegisterToRegister(tc.n)
			require.EqualError(t, err, tc.expErr)
		}
	})

	const inst = asm_arm64.ADD
	for _, tc := range []struct {
		srcReg, shiftedSrcReg, dstReg asm.Register
		shiftNum                      int64
	}{
		{
			srcReg:        asm_arm64.REG_R0,
			shiftedSrcReg: asm_arm64.REG_R29,
			shiftNum:      1,
			dstReg:        asm_arm64.REG_R21,
		},
		{
			srcReg:        asm_arm64.REG_R0,
			shiftedSrcReg: asm_arm64.REG_R29,
			shiftNum:      2,
			dstReg:        asm_arm64.REG_R21,
		},
		{
			srcReg:        asm_arm64.REG_R0,
			shiftedSrcReg: asm_arm64.REG_R29,
			shiftNum:      8,
			dstReg:        asm_arm64.REG_R21,
		},
		{
			srcReg:        asm_arm64.REG_R29,
			shiftedSrcReg: asm_arm64.REG_R0,
			shiftNum:      16,
			dstReg:        asm_arm64.REG_R21,
		},
		{
			srcReg:        asm_arm64.REG_R29,
			shiftedSrcReg: asm_arm64.REG_R0,
			shiftNum:      64,
			dstReg:        asm_arm64.REG_R21,
		},
		{
			srcReg:        asm_arm64.REGZERO,
			shiftedSrcReg: asm_arm64.REG_R0,
			shiftNum:      64,
			dstReg:        asm_arm64.REG_R21,
		},
		{
			srcReg:        asm_arm64.REGZERO,
			shiftedSrcReg: asm_arm64.REGZERO,
			shiftNum:      64,
			dstReg:        asm_arm64.REG_R21,
		},
		{
			srcReg:        asm_arm64.REGZERO,
			shiftedSrcReg: asm_arm64.REGZERO,
			shiftNum:      64,
			dstReg:        asm_arm64.REGZERO,
		},
	} {
		tc := tc
		t.Run(fmt.Sprintf("src=%s,shifted_src=%s,shift_num=%d,dst=%s",
			asm_arm64.RegisterName(tc.srcReg), asm_arm64.RegisterName(tc.shiftedSrcReg),
			tc.shiftNum, asm_arm64.RegisterName(tc.srcReg)), func(t *testing.T) {

			// TODO: remove golang-asm dependency in tests.
			goasm := newGoasmAssembler(t, asm.NilRegister)
			goasm.CompileLeftShiftedRegisterToRegister(inst, tc.shiftedSrcReg, tc.shiftNum, tc.srcReg, tc.dstReg)
			expected, err := goasm.Assemble()
			require.NoError(t, err)

			a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
			err = a.EncodeLeftShiftedRegisterToRegister(&asm_arm64.NodeImpl{Instruction: inst,
				SrcReg: tc.srcReg, SrcReg2: tc.shiftedSrcReg, SrcConst: tc.shiftNum,
				DstReg: tc.dstReg,
			})
			require.NoError(t, err)

			actual := a.Bytes()
			require.Equal(t, expected, actual)
		})
	}
}

func TestAssemblerImpl_EncodeTwoRegistersToNone(t *testing.T) {
	t.Run("error", func(t *testing.T) {
		for _, tc := range []struct {
			n      *asm_arm64.NodeImpl
			expErr string
		}{
			{
				n: &asm_arm64.NodeImpl{Instruction: asm_arm64.SUB, Types: asm_arm64.OperandTypesTwoRegistersToNone,
					SrcReg: asm_arm64.REG_R0, SrcReg2: asm_arm64.REG_R0, DstReg: asm_arm64.REG_R0},
				expErr: "SUB is unsupported for from:two-registers,to:none type",
			},
			{
				n: &asm_arm64.NodeImpl{Instruction: asm_arm64.CMP,
					SrcReg: asm_arm64.REG_R0, SrcReg2: asm_arm64.REG_F0},
				expErr: "F0 is not integer",
			},
			{
				n: &asm_arm64.NodeImpl{Instruction: asm_arm64.FCMPS,
					SrcReg: asm_arm64.REG_R0, SrcReg2: asm_arm64.REG_F0},
				expErr: "R0 is not float",
			},
		} {
			a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
			err := a.EncodeTwoRegistersToNone(tc.n)
			require.EqualError(t, err, tc.expErr)
		}
	})

	intRegs := []asm.Register{asm_arm64.REGZERO, asm_arm64.REG_R0, asm_arm64.REG_R10, asm_arm64.REG_R30}
	floatRegs := []asm.Register{asm_arm64.REG_F0, asm_arm64.REG_F12, asm_arm64.REG_F31}
	for _, tc := range []struct {
		instruction asm.Instruction
		regs        []asm.Register
	}{
		{instruction: asm_arm64.CMP, regs: intRegs},
		{instruction: asm_arm64.CMPW, regs: intRegs},
		{instruction: asm_arm64.FCMPD, regs: floatRegs},
		{instruction: asm_arm64.FCMPS, regs: floatRegs},
	} {
		t.Run(asm_arm64.InstructionName(tc.instruction), func(t *testing.T) {
			for _, src := range tc.regs {
				for _, src2 := range tc.regs {
					t.Run(fmt.Sprintf("src=%s,src2=%s", asm_arm64.RegisterName(src), asm_arm64.RegisterName(src2)), func(t *testing.T) {
						goasm := newGoasmAssembler(t, asm.NilRegister)
						goasm.CompileTwoRegistersToNone(tc.instruction, src, src2)
						expected, err := goasm.Assemble()
						require.NoError(t, err)

						a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
						err = a.EncodeTwoRegistersToNone(&asm_arm64.NodeImpl{Instruction: tc.instruction, SrcReg: src, SrcReg2: src2})
						require.NoError(t, err)

						actual := a.Bytes()
						require.Equal(t, expected, actual)
					})

				}
			}
		})
	}
}

func TestAssemblerImpl_EncodeThreeRegistersToRegistere(t *testing.T) {
	intRegs := []asm.Register{asm_arm64.REGZERO, asm_arm64.REG_R1, asm_arm64.REG_R10, asm_arm64.REG_R30}
	for _, inst := range []asm.Instruction{asm_arm64.MSUB, asm_arm64.MSUBW} {
		inst := inst
		t.Run(asm_arm64.InstructionName(inst), func(t *testing.T) {
			for _, src1 := range intRegs {
				for _, src2 := range intRegs {
					for _, src3 := range intRegs {
						for _, dst := range intRegs {
							src1, src2, src3, dst := src1, src2, src3, dst
							t.Run(fmt.Sprintf("src1=%s,src2=%s,src3=%s,dst=%s",
								asm_arm64.RegisterName(src1), asm_arm64.RegisterName(src2),
								asm_arm64.RegisterName(src3), asm_arm64.RegisterName(dst)), func(t *testing.T) {
								goasm := newGoasmAssembler(t, asm.NilRegister)
								goasm.CompileThreeRegistersToRegister(inst, src1, src2, src3, dst)
								expected, err := goasm.Assemble()
								require.NoError(t, err)

								a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
								err = a.EncodeThreeRegistersToRegister(&asm_arm64.NodeImpl{Instruction: inst, SrcReg: src1, SrcReg2: src2, DstReg: src3, DstReg2: dst})
								require.NoError(t, err)

								actual := a.Bytes()
								require.Equal(t, expected, actual)
							})
						}
					}
				}
			}
		})
	}
}
