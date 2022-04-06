package arm64debug

import (
	"encoding/hex"
	"fmt"
	"math"
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

func TestAssemblerImpl_EncodeThreeRegistersToRegister(t *testing.T) {
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

func TestAssemblerImpl_EncodeRegisterToRegister(t *testing.T) {
	t.Run("error", func(t *testing.T) {
		for _, tc := range []struct {
			n      *asm_arm64.NodeImpl
			expErr string
		}{
			{
				n: &asm_arm64.NodeImpl{Instruction: asm_arm64.ADR, Types: asm_arm64.OperandTypesRegisterToRegister,
					SrcReg: asm_arm64.REG_R0, SrcReg2: asm_arm64.REG_R0, DstReg: asm_arm64.REG_R0},
				expErr: "ADR is unsupported for from:register,to:register type",
			},
		} {
			a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
			err := a.EncodeRegisterToRegister(tc.n)
			require.EqualError(t, err, tc.expErr)
		}
	})

	intRegs := []asm.Register{asm_arm64.REGZERO, asm_arm64.REG_R1, asm_arm64.REG_R10, asm_arm64.REG_R30}
	intRegsWithoutZero := intRegs[1:]
	conditionalRegs := []asm.Register{asm_arm64.REG_COND_EQ, asm_arm64.REG_COND_NE, asm_arm64.REG_COND_HS, asm_arm64.REG_COND_LO, asm_arm64.REG_COND_MI, asm_arm64.REG_COND_PL, asm_arm64.REG_COND_VS, asm_arm64.REG_COND_VC, asm_arm64.REG_COND_HI, asm_arm64.REG_COND_LS, asm_arm64.REG_COND_GE, asm_arm64.REG_COND_LT, asm_arm64.REG_COND_GT, asm_arm64.REG_COND_LE, asm_arm64.REG_COND_AL, asm_arm64.REG_COND_NV}
	floatRegs := []asm.Register{asm_arm64.REG_F0, asm_arm64.REG_F15, asm_arm64.REG_F31}

	for _, tc := range []struct {
		inst             asm.Instruction
		srcRegs, dstRegs []asm.Register
	}{
		{inst: asm_arm64.ADD, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.ADDW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.SUB, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.CLZ, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.CLZW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.CSET, srcRegs: conditionalRegs, dstRegs: intRegs},
		{inst: asm_arm64.FABSS, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FABSD, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FNEGS, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FNEGD, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FSQRTD, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FSQRTS, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FCVTDS, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FCVTSD, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FRINTMD, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FRINTMS, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FRINTND, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FRINTNS, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FRINTPD, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FRINTPS, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FRINTZD, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FRINTZS, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FDIVS, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FDIVD, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FMAXD, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FMAXS, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FMIND, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FMINS, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FMULS, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FMULD, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FADDD, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FADDS, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FCVTZSD, srcRegs: floatRegs, dstRegs: intRegs},
		{inst: asm_arm64.FCVTZSDW, srcRegs: floatRegs, dstRegs: intRegs},
		{inst: asm_arm64.FCVTZSS, srcRegs: floatRegs, dstRegs: intRegs},
		{inst: asm_arm64.FCVTZSSW, srcRegs: floatRegs, dstRegs: intRegs},
		{inst: asm_arm64.FCVTZUD, srcRegs: floatRegs, dstRegs: intRegs},
		{inst: asm_arm64.FCVTZUDW, srcRegs: floatRegs, dstRegs: intRegs},
		{inst: asm_arm64.FCVTZUS, srcRegs: floatRegs, dstRegs: intRegs},
		{inst: asm_arm64.FCVTZUSW, srcRegs: floatRegs, dstRegs: intRegs},
		{inst: asm_arm64.FMOVD, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FMOVS, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FMOVD, srcRegs: intRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FMOVS, srcRegs: intRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FMOVD, srcRegs: floatRegs, dstRegs: intRegs},
		{inst: asm_arm64.FMOVS, srcRegs: floatRegs, dstRegs: intRegs},
		{inst: asm_arm64.MOVD, srcRegs: intRegs, dstRegs: intRegsWithoutZero},
		{inst: asm_arm64.MOVWU, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.MRS, srcRegs: []asm.Register{asm_arm64.REG_FPSR}, dstRegs: intRegs},
		{inst: asm_arm64.MSR, srcRegs: intRegs, dstRegs: []asm.Register{asm_arm64.REG_FPSR}},
		{inst: asm_arm64.MUL, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.MULW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.NEG, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.NEGW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.RBIT, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.RBITW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.SDIV, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.SDIVW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.UDIV, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.UDIVW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.SCVTFD, srcRegs: intRegs, dstRegs: floatRegs},
		{inst: asm_arm64.SCVTFWD, srcRegs: intRegs, dstRegs: floatRegs},
		{inst: asm_arm64.SCVTFS, srcRegs: intRegs, dstRegs: floatRegs},
		{inst: asm_arm64.SCVTFWS, srcRegs: intRegs, dstRegs: floatRegs},
		{inst: asm_arm64.UCVTFD, srcRegs: intRegs, dstRegs: floatRegs},
		{inst: asm_arm64.UCVTFWD, srcRegs: intRegs, dstRegs: floatRegs},
		{inst: asm_arm64.UCVTFS, srcRegs: intRegs, dstRegs: floatRegs},
		{inst: asm_arm64.UCVTFWS, srcRegs: intRegs, dstRegs: floatRegs},
		{inst: asm_arm64.SXTB, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.SXTBW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.SXTH, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.SXTHW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.SXTW, srcRegs: intRegs, dstRegs: intRegs},
	} {

		tc := tc
		t.Run(asm_arm64.InstructionName(tc.inst), func(t *testing.T) {
			for _, src := range tc.srcRegs {
				for _, dst := range tc.dstRegs {
					src, dst := src, dst
					t.Run(fmt.Sprintf("src=%s,dst=%s", asm_arm64.RegisterName(src), asm_arm64.RegisterName(dst)), func(t *testing.T) {
						goasm := newGoasmAssembler(t, asm.NilRegister)
						if tc.inst == asm_arm64.CSET {

							goasm.CompileConditionalRegisterSet(conditionalRegisterToState(src), dst)
						} else {
							goasm.CompileRegisterToRegister(tc.inst, src, dst)

						}
						expected, err := goasm.Assemble()
						require.NoError(t, err)

						a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
						err = a.EncodeRegisterToRegister(&asm_arm64.NodeImpl{Instruction: tc.inst, SrcReg: src, DstReg: dst})
						require.NoError(t, err)

						actual := a.Bytes()
						require.Equal(t, expected, actual)
					})
				}
			}
		})
	}
}

func TestAssemblerImpl_EncodeTwoRegistersToRegister(t *testing.T) {
	t.Run("error", func(t *testing.T) {
		for _, tc := range []struct {
			n      *asm_arm64.NodeImpl
			expErr string
		}{
			{
				n: &asm_arm64.NodeImpl{Instruction: asm_arm64.ADR, Types: asm_arm64.OperandTypesTwoRegistersToRegister,
					SrcReg: asm_arm64.REG_R0, SrcReg2: asm_arm64.REG_R0, DstReg: asm_arm64.REG_R0},
				expErr: "ADR is unsupported for from:two-registers,to:register type",
			},
		} {
			a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
			err := a.EncodeThreeRegistersToRegister(tc.n)
			require.EqualError(t, err, tc.expErr)
		}
	})

	intRegs := []asm.Register{asm_arm64.REGZERO, asm_arm64.REG_R1, asm_arm64.REG_R10, asm_arm64.REG_R30}
	floatRegs := []asm.Register{asm_arm64.REG_F0, asm_arm64.REG_F15, asm_arm64.REG_F31}

	for _, tc := range []struct {
		inst             asm.Instruction
		srcRegs, dstRegs []asm.Register
	}{
		{inst: asm_arm64.AND, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.ANDW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.ORR, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.ORRW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.EOR, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.EORW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.ASR, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.ASRW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.LSL, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.LSLW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.LSR, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.LSRW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.ROR, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.RORW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.SDIV, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.SDIVW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.UDIV, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.UDIVW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.SUB, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.SUBW, srcRegs: intRegs, dstRegs: intRegs},
		{inst: asm_arm64.FSUBD, srcRegs: floatRegs, dstRegs: floatRegs},
		{inst: asm_arm64.FSUBS, srcRegs: floatRegs, dstRegs: floatRegs},
	} {
		tc := tc
		t.Run(asm_arm64.InstructionName(tc.inst), func(t *testing.T) {
			for _, src := range tc.srcRegs {
				for _, src2 := range tc.srcRegs {
					for _, dst := range tc.dstRegs {
						src, src2, dst := src, src2, dst
						t.Run(fmt.Sprintf("src=%s,src2=%s,dst=%s", asm_arm64.RegisterName(src), asm_arm64.RegisterName(src2), asm_arm64.RegisterName(dst)), func(t *testing.T) {
							goasm := newGoasmAssembler(t, asm.NilRegister)
							goasm.CompileTwoRegistersToRegister(tc.inst, src, src2, dst)
							expected, err := goasm.Assemble()
							require.NoError(t, err)

							a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
							err = a.EncodeTwoRegistersToRegister(&asm_arm64.NodeImpl{Instruction: tc.inst, SrcReg: src, SrcReg2: src2, DstReg: dst})
							require.NoError(t, err)

							actual := a.Bytes()
							require.Equal(t, expected, actual)
						})
					}
				}
			}
		})
	}
}

func TestAssemblerImpl_EncodeRegisterAndConstToNone(t *testing.T) {
	t.Run("error", func(t *testing.T) {
		for _, tc := range []struct {
			n      *asm_arm64.NodeImpl
			expErr string
		}{
			{
				n: &asm_arm64.NodeImpl{Instruction: asm_arm64.ADR, Types: asm_arm64.OperandTypesRegisterAndConstToNone,
					SrcReg: asm_arm64.REG_R0, SrcReg2: asm_arm64.REG_R0, DstReg: asm_arm64.REG_R0},
				expErr: "ADR is unsupported for from:register-and-const,to:none type",
			},
			{
				n: &asm_arm64.NodeImpl{Instruction: asm_arm64.CMP, Types: asm_arm64.OperandTypesRegisterAndConstToNone,
					SrcReg: asm_arm64.REG_R0, SrcConst: 12345},
				expErr: "immediate for CMP must fit in 0 to 4095 but got 12345",
			},
			{
				n: &asm_arm64.NodeImpl{Instruction: asm_arm64.CMP, Types: asm_arm64.OperandTypesRegisterAndConstToNone,
					SrcReg: asm_arm64.REGZERO, SrcConst: 123},
				expErr: "zero register is not supported for CMP (immediate)",
			},
		} {
			a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
			err := a.EncodeRegisterAndConstToNone(tc.n)
			require.EqualError(t, err, tc.expErr)
		}
	})

	const inst = asm_arm64.CMP
	for _, reg := range []asm.Register{asm_arm64.REG_R1, asm_arm64.REG_R10, asm_arm64.REG_R30} {
		for _, c := range []int64{0, 10, 100, 300, 4095} {
			reg, c := reg, c
			t.Run(fmt.Sprintf("%s, %d", asm_arm64.RegisterName(reg), c), func(t *testing.T) {
				goasm := newGoasmAssembler(t, asm.NilRegister)
				goasm.CompileRegisterAndConstToNone(inst, reg, c)
				expected, err := goasm.Assemble()
				require.NoError(t, err)
				if c == 0 {
					// This case cannot be supported in golang-asm and it results in miscompilation.
					expected[3] = 0b111_10001
				}

				a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
				err = a.EncodeRegisterAndConstToNone(&asm_arm64.NodeImpl{Instruction: inst, SrcReg: reg, SrcConst: c})
				require.NoError(t, err)

				actual := a.Bytes()
				require.Equal(t, expected, actual)
			})
		}
	}
}

func TestAssemblerImpl_EncodeConstToRegister(t *testing.T) {
	t.Run("error", func(t *testing.T) {
		for _, tc := range []struct {
			n      *asm_arm64.NodeImpl
			expErr string
		}{
			{
				n: &asm_arm64.NodeImpl{Instruction: asm_arm64.ADR, Types: asm_arm64.OperandTypesConstToRegister,
					SrcReg: asm_arm64.REG_R0, SrcReg2: asm_arm64.REG_R0, DstReg: asm_arm64.REG_R0},
				expErr: "ADR is unsupported for from:const,to:register type",
			},
		} {
			a := asm_arm64.NewAssemblerImpl(asm.NilRegister)
			err := a.EncodeConstToRegister(tc.n)
			require.EqualError(t, err, tc.expErr)
		}
	})

	for _, tc := range []struct {
		inst   asm.Instruction
		consts []int64
	}{
		// {
		// 	inst: asm_arm64.ADD,
		// 	consts: []int64{
		// 		// 1) https://github.com/twitchyliquid64/golang-asm/blob/v0.15.1/obj/arm64/asm7.go#L3035-L3052
		// 		0x1,
		// 		0xfff,
		// 		0xfff << 12,
		// 		123 << 12,

		// 		// 2) https://github.com/twitchyliquid64/golang-asm/blob/v0.15.1/obj/arm64/asm7.go#L4081-L4109
		(1<<15 + 1),
		(1<<15 + 1) << 16,
		(1<<15 + 1) << 32,

		// 		// 3) https://github.com/twitchyliquid64/golang-asm/blob/v0.15.1/obj/arm64/asm7.go#L4081-L4109
		// 		0x0000_ffff_ffff_ffff,
		// 		-281470681743361, /* = 0xffff_0000_ffff_ffff */

		// 		// 4) https://github.com/twitchyliquid64/golang-asm/blob/v0.15.1/obj/arm64/asm7.go#L6719-L6733
		// 		math.MinInt32 + 1,
		// 		-281474976645121, /* = 0xffff_0000_0000_ffff */

		// 		// 5) https://github.com/twitchyliquid64/golang-asm/blob/v0.15.1/obj/arm64/asm7.go#L3901-L3914
		// 		1<<20 + 1,
		// 		1<<20 - 1,
		// 		1<<23 | 0b01,

		// 		// 6) https://github.com/twitchyliquid64/golang-asm/blob/v0.15.1/obj/arm64/asm7.go#L3215-L3256
		// 		// TODO:
		// 		// movz x27, #0x1‰
		// 		// movk x27, #0x4000, lsl #16
		// 		// add  x30, x30, x27
		// 		// 1<<30 + 1,
		// 	},
		// },
		// {
		// 	inst: asm_arm64.MOVW,
		// 	consts: []int64{
		// 		1 << 1, 1<<1 + 1, 1<<1 - 1, 1<<1 + 0xf,
		// 		1 << 2, 1<<2 + 1, 1<<2 - 1, 1<<2 + 0xf,
		// 		1 << 3, 1<<3 + 1, 1<<3 - 1, 1<<3 + 0xf,
		// 		1 << 4, 1<<4 + 1, 1<<4 - 1, 1<<4 + 0xf,
		// 		1 << 5, 1<<5 + 1, 1<<5 - 1, 1<<5 + 0xf,
		// 		1 << 6, 1<<6 + 1, 1<<6 - 1, 1<<6 + 0xf,
		// 		0xfff << 1, 0xfff<<1 - 1, 0xfff<<1 + 1,
		// 		0, 1, -1, 2, 3, 10, -10, 123, -123,
		// 		math.MaxInt16, math.MaxInt32, math.MaxUint32, 0b01000000_00000010, 0xffff_0000, 0xffff_0001, 0xf00_000f,
		// 		math.MaxInt16 - 1, math.MaxInt32 - 1, math.MaxUint32 - 1, 0b01000000_00000010 - 1, 0xffff_0000 - 1, 0xffff_0001 - 1, 0xf00_000f - 1,
		// 		math.MaxInt16 + 1, 0b01000000_00001010 - 1, 0xfff_0000 - 1, 0xffe_0001 - 1, 0xe00_000f - 1,
		// 		(1<<15 + 1) << 16, 0b1_00000000_00000010,
		// 	},
		// },
		// {
		// 	inst: asm_arm64.MOVW,
		// 	consts: []int64{
		// 		1 << 1, 1<<1 + 1, 1<<1 - 1, 1<<1 + 0xf,
		// 		1 << 2, 1<<2 + 1, 1<<2 - 1, 1<<2 + 0xf,
		// 		1 << 3, 1<<3 + 1, 1<<3 - 1, 1<<3 + 0xf,
		// 		1 << 4, 1<<4 + 1, 1<<4 - 1, 1<<4 + 0xf,
		// 		1 << 5, 1<<5 + 1, 1<<5 - 1, 1<<5 + 0xf,
		// 		1 << 6, 1<<6 + 1, 1<<6 - 1, 1<<6 + 0xf,
		// 		0xfff << 1, 0xfff<<1 - 1, 0xfff<<1 + 1,
		// 		0, 1, -1, 2, 3, 10, -10, 123, -123,
		// 		math.MaxInt16, math.MaxInt32, math.MaxUint32, 0b01000000_00000010, 0xffff_0000, 0xffff_0001, 0xf00_000f,
		// 		math.MaxInt16 - 1, math.MaxInt32 - 1, math.MaxUint32 - 1, 0b01000000_00000010 - 1, 0xffff_0000 - 1, 0xffff_0001 - 1, 0xf00_000f - 1,
		// 		math.MaxInt16 + 1, 0b01000000_00001010 - 1, 0xfff_0000 - 1, 0xffe_0001 - 1, 0xe00_000f - 1,
		// 		(1<<15 + 1) << 16, 0b1_00000000_00000010,
		// 	},
		// },
		{
			inst: asm_arm64.MOVD,
			consts: []int64{
				1 << 1, 1<<1 + 1, 1<<1 - 1, 1<<1 + 0xf,
				1 << 2, 1<<2 + 1, 1<<2 - 1, 1<<2 + 0xf,
				1 << 3, 1<<3 + 1, 1<<3 - 1, 1<<3 + 0xf,
				1 << 4, 1<<4 + 1, 1<<4 - 1, 1<<4 + 0xf,
				1 << 5, 1<<5 + 1, 1<<5 - 1, 1<<5 + 0xf,
				1 << 6, 1<<6 + 1, 1<<6 - 1, 1<<6 + 0xf,
				0xfff << 1, 0xfff<<1 - 1, 0xfff<<1 + 1,
				0, 1, -1, 2, 3, 10, -10, 123, -123,
				math.MaxInt16, math.MaxInt32, math.MaxUint32, 0b01000000_00000010, 0xffff_0000, 0xffff_0001, 0xf00_000f,
				math.MaxInt16 - 1, math.MaxInt32 - 1, math.MaxUint32 - 1, 0b01000000_00000010 - 1, 0xffff_0000 - 1, 0xffff_0001 - 1, 0xf00_000f - 1,
				math.MaxInt16 + 1, 0b01000000_00001010 - 1,
				0xfff_0000 - 1,
				0xffe_0001 - 1,
				0xe00_000f - 1,
				(1<<15 + 1) << 16,
				0b1_00000000_00000010,
				1 << 32, 1 << 34, 1 << 40,
				1<<32 + 1, 1<<34 + 1, 1<<40 + 1,
				1<<32 - 1, 1<<34 - 1, 1<<40 - 1,
				1<<32 + 0xf, 1<<34 + 0xf, 1<<40 + 0xf,
				1<<32 - 0xf, 1<<34 - 0xf, 1<<40 - 0xf,
				math.MaxInt64, math.MinInt64,
			},
		},
	} {
		tc := tc
		t.Run(asm_arm64.InstructionName(tc.inst), func(t *testing.T) {
			for _, r := range []asm.Register{
				// asm_arm64.REG_R0, asm_arm64.REG_R10,
				asm_arm64.REG_R30,
			} {
				r := r
				t.Run(asm_arm64.RegisterName(r), func(t *testing.T) {
					for _, c := range tc.consts {
						c := c
						t.Run(fmt.Sprintf("0x%x", uint64(c)), func(t *testing.T) {
							goasm := newGoasmAssembler(t, asm_arm64.REG_R27)
							goasm.CompileConstToRegister(tc.inst, c, r)
							expected, err := goasm.Assemble()
							require.NoError(t, err)

							a := asm_arm64.NewAssemblerImpl(asm_arm64.REG_R27)
							err = a.EncodeConstToRegister(&asm_arm64.NodeImpl{Instruction: tc.inst, SrcConst: c, DstReg: r})
							require.NoError(t, err)

							fmt.Println(hex.EncodeToString(expected))

							actual := a.Bytes()
							fmt.Println(hex.EncodeToString(actual))
							require.Equal(t, expected, actual)

						})
					}
				})
			}
		})
	}
}

func conditionalRegisterToState(r asm.Register) asm.ConditionalRegisterState {
	switch r {
	case asm_arm64.REG_COND_EQ:
		return asm_arm64.COND_EQ
	case asm_arm64.REG_COND_NE:
		return asm_arm64.COND_NE
	case asm_arm64.REG_COND_HS:
		return asm_arm64.COND_HS
	case asm_arm64.REG_COND_LO:
		return asm_arm64.COND_LO
	case asm_arm64.REG_COND_MI:
		return asm_arm64.COND_MI
	case asm_arm64.REG_COND_PL:
		return asm_arm64.COND_PL
	case asm_arm64.REG_COND_VS:
		return asm_arm64.COND_VS
	case asm_arm64.REG_COND_VC:
		return asm_arm64.COND_VC
	case asm_arm64.REG_COND_HI:
		return asm_arm64.COND_HI
	case asm_arm64.REG_COND_LS:
		return asm_arm64.COND_LS
	case asm_arm64.REG_COND_GE:
		return asm_arm64.COND_GE
	case asm_arm64.REG_COND_LT:
		return asm_arm64.COND_LT
	case asm_arm64.REG_COND_GT:
		return asm_arm64.COND_GT
	case asm_arm64.REG_COND_LE:
		return asm_arm64.COND_LE
	case asm_arm64.REG_COND_AL:
		return asm_arm64.COND_AL
	case asm_arm64.REG_COND_NV:
		return asm_arm64.COND_NV
	}
	return asm.ConditionalRegisterStateUnset
}
