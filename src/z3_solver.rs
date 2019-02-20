// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use crate::constant_domain::ConstantDomain;
use crate::expression::{Expression, ExpressionType};
use crate::smt_solver::SmtResult;
use crate::smt_solver::SmtSolver;

use std::convert::TryFrom;
use std::ffi::CStr;
use std::ffi::CString;
use std::sync::Mutex;
use z3_sys;

pub type Z3ExpressionType = z3_sys::Z3_ast;

lazy_static! {
    static ref Z3_MUTEX: Mutex<()> = Mutex::new(());
}

pub struct Z3Solver {
    z3_context: z3_sys::Z3_context,
    z3_solver: z3_sys::Z3_solver,
    any_sort: z3_sys::Z3_sort,
    bool_sort: z3_sys::Z3_sort,
    int_sort: z3_sys::Z3_sort,
    f32_sort: z3_sys::Z3_sort,
    f64_sort: z3_sys::Z3_sort,
    nearest_even: z3_sys::Z3_ast,
    zero: z3_sys::Z3_ast,
    one: z3_sys::Z3_ast,
    empty_str: z3_sys::Z3_string,
}

impl Z3Solver {
    pub fn new() -> Z3Solver {
        unsafe {
            let _guard = Z3_MUTEX.lock().unwrap();
            let z3_sys_cfg = z3_sys::Z3_mk_config();
            let time_out = CString::new("timeout").unwrap().into_raw();
            let ms = CString::new("100").unwrap().into_raw();
            z3_sys::Z3_set_param_value(z3_sys_cfg, time_out, ms);

            let z3_context = z3_sys::Z3_mk_context(z3_sys_cfg);
            let z3_solver = z3_sys::Z3_mk_solver(z3_context);
            let empty_str = CString::new("").unwrap().into_raw();
            let symbol = z3_sys::Z3_mk_string_symbol(z3_context, empty_str);

            let any_sort = z3_sys::Z3_mk_uninterpreted_sort(z3_context, symbol);
            let bool_sort = { z3_sys::Z3_mk_bool_sort(z3_context) };
            let int_sort = { z3_sys::Z3_mk_int_sort(z3_context) };
            let f32_sort = { z3_sys::Z3_mk_fpa_sort_32(z3_context) };
            let f64_sort = { z3_sys::Z3_mk_fpa_sort_64(z3_context) };
            let nearest_even = { z3_sys::Z3_mk_fpa_round_nearest_ties_to_even(z3_context) };
            let zero = { z3_sys::Z3_mk_int(z3_context, 0, int_sort) };
            let one = { z3_sys::Z3_mk_int(z3_context, 1, int_sort) };

            Z3Solver {
                z3_context,
                z3_solver,
                any_sort,
                bool_sort,
                int_sort,
                f32_sort,
                f64_sort,
                nearest_even,
                zero,
                one,
                empty_str,
            }
        }
    }
}

impl Default for Z3Solver {
    fn default() -> Self {
        Z3Solver::new()
    }
}

impl SmtSolver<Z3ExpressionType> for Z3Solver {
    fn as_debug_string(&self, expression: &Z3ExpressionType) -> String {
        unsafe {
            let debug_str_bytes = z3_sys::Z3_ast_to_string(self.z3_context, *expression);
            let debug_str = CStr::from_ptr(debug_str_bytes);
            String::from(debug_str.to_str().unwrap())
        }
    }

    fn assert(&mut self, expression: &Z3ExpressionType) {
        unsafe {
            z3_sys::Z3_solver_assert(self.z3_context, self.z3_solver, *expression);
        }
    }

    fn backtrack(&mut self) {
        unsafe {
            z3_sys::Z3_solver_pop(self.z3_context, self.z3_solver, 1);
        }
    }

    fn get_as_smt_predicate(&mut self, mirai_expression: &Expression) -> Z3ExpressionType {
        self.get_as_bool_z3_ast(mirai_expression)
    }

    fn set_backtrack_position(&mut self) {
        unsafe {
            z3_sys::Z3_solver_push(self.z3_context, self.z3_solver);
        }
    }

    fn solve(&mut self) -> SmtResult {
        unsafe {
            match z3_sys::Z3_solver_check(self.z3_context, self.z3_solver) {
                z3_sys::Z3_L_TRUE => SmtResult::Satisfiable,
                z3_sys::Z3_L_FALSE => SmtResult::Unsatisfiable,
                z3_sys::Z3_L_UNDEF | _ => SmtResult::Undefined,
            }
        }
    }
}

impl Z3Solver {
    pub fn get_as_z3_ast(&self, expression: &Expression) -> z3_sys::Z3_ast {
        match expression {
            Expression::Add { .. }
            | Expression::Div { .. }
            | Expression::Mul { .. }
            | Expression::Rem { .. }
            | Expression::Sub { .. } => self.get_as_numeric_z3_ast(expression).1,
            Expression::AddOverflows {
                left,
                right,
                result_type,
            } => {
                let num_bits = u32::from(result_type.bit_length());
                let is_signed = result_type.is_signed_integer();
                let left_bv = self.get_as_bv_z3_ast(&(**left).expression, num_bits);
                let right_bv = self.get_as_bv_z3_ast(&(**right).expression, num_bits);
                unsafe {
                    let does_not_overflow = z3_sys::Z3_mk_bvadd_no_overflow(
                        self.z3_context,
                        left_bv,
                        right_bv,
                        is_signed,
                    );
                    if is_signed {
                        let does_not_underflow =
                            z3_sys::Z3_mk_bvadd_no_underflow(self.z3_context, left_bv, right_bv);
                        let tmp = vec![does_not_overflow, does_not_underflow];
                        let stays_in_range = z3_sys::Z3_mk_and(self.z3_context, 2, tmp.as_ptr());
                        z3_sys::Z3_mk_not(self.z3_context, stays_in_range)
                    } else {
                        z3_sys::Z3_mk_not(self.z3_context, does_not_overflow)
                    }
                }
            }
            Expression::And { left, right } => {
                let left_ast = self.get_as_bool_z3_ast(&(**left).expression);
                let right_ast = self.get_as_bool_z3_ast(&(**right).expression);
                unsafe {
                    let tmp = vec![left_ast, right_ast];
                    z3_sys::Z3_mk_and(self.z3_context, 2, tmp.as_ptr())
                }
            }
            Expression::BitAnd { .. } | Expression::BitOr { .. } | Expression::BitXor { .. } => {
                self.get_as_bv_z3_ast(expression, 128)
            }
            Expression::CompileTimeConstant(const_domain) => match const_domain {
                ConstantDomain::Char(v) => unsafe {
                    z3_sys::Z3_mk_int(self.z3_context, i32::from(*v as u16), self.int_sort)
                },
                ConstantDomain::False => unsafe { z3_sys::Z3_mk_false(self.z3_context) },
                ConstantDomain::I128(v) => unsafe {
                    let v64 = i64::try_from(*v);
                    if v64.is_ok() {
                        z3_sys::Z3_mk_int64(self.z3_context, v64.unwrap(), self.int_sort)
                    } else {
                        let num_str = format!("{}", *v);
                        let c_string = CString::new(num_str).unwrap();
                        z3_sys::Z3_mk_numeral(self.z3_context, c_string.into_raw(), self.int_sort)
                    }
                },
                ConstantDomain::F32(v) => unsafe {
                    let fv = f32::from_bits(*v);
                    z3_sys::Z3_mk_fpa_numeral_float(self.z3_context, fv, self.f32_sort)
                },
                ConstantDomain::F64(v) => unsafe {
                    let fv = f64::from_bits(*v);
                    z3_sys::Z3_mk_fpa_numeral_double(self.z3_context, fv, self.f64_sort)
                },
                ConstantDomain::U128(v) => unsafe {
                    let v64 = u64::try_from(*v);
                    if v64.is_ok() {
                        z3_sys::Z3_mk_unsigned_int64(self.z3_context, v64.unwrap(), self.int_sort)
                    } else {
                        let num_str = format!("{}", *v);
                        let c_string = CString::new(num_str).unwrap();
                        z3_sys::Z3_mk_numeral(self.z3_context, c_string.into_raw(), self.int_sort)
                    }
                },
                ConstantDomain::True => unsafe { z3_sys::Z3_mk_true(self.z3_context) },
                _ => unsafe {
                    z3_sys::Z3_mk_fresh_const(self.z3_context, self.empty_str, self.any_sort)
                },
            },
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                let condition_ast = self.get_as_bool_z3_ast(&(**condition).expression);
                let consequent_ast = self.get_as_z3_ast(&(**consequent).expression);
                let alternate_ast = self.get_as_z3_ast(&(**alternate).expression);
                unsafe {
                    z3_sys::Z3_mk_ite(
                        self.z3_context,
                        condition_ast,
                        consequent_ast,
                        alternate_ast,
                    )
                }
            }
            Expression::Equals { left, right } => {
                let (lf, left_ast) = self.get_as_numeric_z3_ast(&(**left).expression);
                let (rf, right_ast) = self.get_as_numeric_z3_ast(&(**right).expression);
                assert_eq!(lf, rf);
                unsafe {
                    if lf {
                        z3_sys::Z3_mk_fpa_eq(self.z3_context, left_ast, right_ast)
                    } else {
                        z3_sys::Z3_mk_eq(self.z3_context, left_ast, right_ast)
                    }
                }
            }
            Expression::GreaterOrEqual { left, right } => {
                let (lf, left_ast) = self.get_as_numeric_z3_ast(&(**left).expression);
                let (rf, right_ast) = self.get_as_numeric_z3_ast(&(**right).expression);
                assert_eq!(lf, rf);
                unsafe {
                    if lf {
                        z3_sys::Z3_mk_fpa_geq(self.z3_context, left_ast, right_ast)
                    } else {
                        z3_sys::Z3_mk_ge(self.z3_context, left_ast, right_ast)
                    }
                }
            }
            Expression::GreaterThan { left, right } => {
                let (lf, left_ast) = self.get_as_numeric_z3_ast(&(**left).expression);
                let (rf, right_ast) = self.get_as_numeric_z3_ast(&(**right).expression);
                assert_eq!(lf, rf);
                unsafe {
                    if lf {
                        z3_sys::Z3_mk_fpa_gt(self.z3_context, left_ast, right_ast)
                    } else {
                        z3_sys::Z3_mk_gt(self.z3_context, left_ast, right_ast)
                    }
                }
            }
            Expression::LessOrEqual { left, right } => {
                let (lf, left_ast) = self.get_as_numeric_z3_ast(&(**left).expression);
                let (rf, right_ast) = self.get_as_numeric_z3_ast(&(**right).expression);
                assert_eq!(lf, rf);
                unsafe {
                    if lf {
                        z3_sys::Z3_mk_fpa_leq(self.z3_context, left_ast, right_ast)
                    } else {
                        z3_sys::Z3_mk_le(self.z3_context, left_ast, right_ast)
                    }
                }
            }
            Expression::LessThan { left, right } => {
                let (lf, left_ast) = self.get_as_numeric_z3_ast(&(**left).expression);
                let (rf, right_ast) = self.get_as_numeric_z3_ast(&(**right).expression);
                assert_eq!(lf, rf);
                unsafe {
                    if lf {
                        z3_sys::Z3_mk_fpa_lt(self.z3_context, left_ast, right_ast)
                    } else {
                        z3_sys::Z3_mk_lt(self.z3_context, left_ast, right_ast)
                    }
                }
            }
            Expression::MulOverflows {
                left,
                right,
                result_type,
            } => {
                let num_bits = u32::from(result_type.bit_length());
                let is_signed = result_type.is_signed_integer();
                let left_bv = self.get_as_bv_z3_ast(&(**left).expression, num_bits);
                let right_bv = self.get_as_bv_z3_ast(&(**right).expression, num_bits);
                unsafe {
                    let does_not_overflow = z3_sys::Z3_mk_bvmul_no_overflow(
                        self.z3_context,
                        left_bv,
                        right_bv,
                        is_signed,
                    );
                    if is_signed {
                        let does_not_underflow =
                            z3_sys::Z3_mk_bvmul_no_underflow(self.z3_context, left_bv, right_bv);
                        let tmp = vec![does_not_overflow, does_not_underflow];
                        let stays_in_range = z3_sys::Z3_mk_and(self.z3_context, 2, tmp.as_ptr());
                        z3_sys::Z3_mk_not(self.z3_context, stays_in_range)
                    } else {
                        z3_sys::Z3_mk_not(self.z3_context, does_not_overflow)
                    }
                }
            }
            Expression::Ne { left, right } => {
                let (lf, left_ast) = self.get_as_numeric_z3_ast(&(**left).expression);
                let (rf, right_ast) = self.get_as_numeric_z3_ast(&(**right).expression);
                assert_eq!(lf, rf);
                unsafe {
                    if lf {
                        let l = z3_sys::Z3_mk_fpa_is_nan(self.z3_context, left_ast);
                        let r = z3_sys::Z3_mk_fpa_is_nan(self.z3_context, right_ast);
                        let eq = z3_sys::Z3_mk_fpa_eq(self.z3_context, left_ast, right_ast);
                        let ne = z3_sys::Z3_mk_not(self.z3_context, eq);
                        let tmp = vec![l, r, ne];
                        z3_sys::Z3_mk_or(self.z3_context, 3, tmp.as_ptr())
                    } else {
                        z3_sys::Z3_mk_not(
                            self.z3_context,
                            z3_sys::Z3_mk_eq(self.z3_context, left_ast, right_ast),
                        )
                    }
                }
            }
            Expression::Neg { operand } => {
                let (is_float, operand_ast) = self.get_as_numeric_z3_ast(&(**operand).expression);
                unsafe {
                    if is_float {
                        z3_sys::Z3_mk_fpa_neg(self.z3_context, operand_ast)
                    } else {
                        z3_sys::Z3_mk_unary_minus(self.z3_context, operand_ast)
                    }
                }
            }
            Expression::Not { operand } => {
                let operand_ast = self.get_as_bool_z3_ast(&(**operand).expression);
                unsafe { z3_sys::Z3_mk_not(self.z3_context, operand_ast) }
            }
            Expression::Or { left, right } => {
                let left_ast = self.get_as_bool_z3_ast(&(**left).expression);
                let right_ast = self.get_as_bool_z3_ast(&(**right).expression);
                unsafe {
                    let tmp = vec![left_ast, right_ast];
                    z3_sys::Z3_mk_or(self.z3_context, 2, tmp.as_ptr())
                }
            }
            Expression::Reference(..) => self.get_as_numeric_z3_ast(expression).1,
            Expression::Shl { left, right } => {
                let left_ast = self.get_as_bv_z3_ast(&(**left).expression, 128);
                let right_ast = self.get_as_bv_z3_ast(&(**right).expression, 128);
                unsafe { z3_sys::Z3_mk_bvshl(self.z3_context, left_ast, right_ast) }
            }
            Expression::Shr {
                left,
                right,
                result_type,
            } => {
                let num_bits = u32::from(result_type.bit_length());
                let left_ast = self.get_as_bv_z3_ast(&(**left).expression, num_bits);
                let right_ast = self.get_as_bv_z3_ast(&(**right).expression, num_bits);
                unsafe {
                    if result_type.is_signed_integer() {
                        z3_sys::Z3_mk_bvashr(self.z3_context, left_ast, right_ast)
                    } else {
                        z3_sys::Z3_mk_bvlshr(self.z3_context, left_ast, right_ast)
                    }
                }
            }
            Expression::ShlOverflows {
                right, result_type, ..
            }
            | Expression::ShrOverflows {
                right, result_type, ..
            } => {
                let (f, right_ast) = self.get_as_numeric_z3_ast(&(**right).expression);
                assert!(!f);
                let num_bits = i32::from(result_type.bit_length());
                unsafe {
                    let num_bits_val = z3_sys::Z3_mk_int(self.z3_context, num_bits, self.int_sort);
                    z3_sys::Z3_mk_ge(self.z3_context, right_ast, num_bits_val)
                }
            }
            Expression::SubOverflows {
                left,
                right,
                result_type,
            } => {
                let num_bits = u32::from(result_type.bit_length());
                let is_signed = result_type.is_signed_integer();
                let left_bv = self.get_as_bv_z3_ast(&(**left).expression, num_bits);
                let right_bv = self.get_as_bv_z3_ast(&(**right).expression, num_bits);
                unsafe {
                    let does_not_underflow = z3_sys::Z3_mk_bvsub_no_underflow(
                        self.z3_context,
                        left_bv,
                        right_bv,
                        is_signed,
                    );
                    if is_signed {
                        let does_not_overflow =
                            z3_sys::Z3_mk_bvsub_no_overflow(self.z3_context, left_bv, right_bv);
                        let tmp = vec![does_not_overflow, does_not_underflow];
                        let stays_in_range = z3_sys::Z3_mk_and(self.z3_context, 2, tmp.as_ptr());
                        z3_sys::Z3_mk_not(self.z3_context, stays_in_range)
                    } else {
                        z3_sys::Z3_mk_not(self.z3_context, does_not_underflow)
                    }
                }
            }
            Expression::Variable { path, var_type } => {
                use self::ExpressionType::*;
                let path_str = CString::new(format!("{:?}", path)).unwrap();
                unsafe {
                    let path_symbol =
                        z3_sys::Z3_mk_string_symbol(self.z3_context, path_str.into_raw());
                    match var_type {
                        Bool => z3_sys::Z3_mk_const(self.z3_context, path_symbol, self.bool_sort),
                        Char | I8 | I16 | I32 | I64 | I128 | Isize | U8 | U16 | U32 | U64
                        | U128 | Usize => {
                            z3_sys::Z3_mk_const(self.z3_context, path_symbol, self.int_sort)
                        }
                        F32 => z3_sys::Z3_mk_const(self.z3_context, path_symbol, self.f32_sort),
                        F64 => z3_sys::Z3_mk_const(self.z3_context, path_symbol, self.f64_sort),
                        NonPrimitive => z3_sys::Z3_mk_fresh_const(
                            self.z3_context,
                            self.empty_str,
                            self.any_sort,
                        ),
                    }
                }
            }
            _ => unsafe {
                info!("uninterpreted expression: {:?}", expression);
                z3_sys::Z3_mk_fresh_const(self.z3_context, self.empty_str, self.any_sort)
            },
        }
    }

    pub fn get_as_numeric_z3_ast(&self, expression: &Expression) -> (bool, z3_sys::Z3_ast) {
        match expression {
            Expression::Add { left, right } => {
                let (lf, left_ast) = self.get_as_numeric_z3_ast(&(**left).expression);
                let (rf, right_ast) = self.get_as_numeric_z3_ast(&(**right).expression);
                assert_eq!(lf, rf);
                unsafe {
                    if lf {
                        (
                            true,
                            z3_sys::Z3_mk_fpa_add(
                                self.z3_context,
                                self.nearest_even,
                                left_ast,
                                right_ast,
                            ),
                        )
                    } else {
                        let tmp = vec![left_ast, right_ast];
                        (false, z3_sys::Z3_mk_add(self.z3_context, 2, tmp.as_ptr()))
                    }
                }
            }
            Expression::Div { left, right } => {
                let (lf, left_ast) = self.get_as_numeric_z3_ast(&(**left).expression);
                let (rf, right_ast) = self.get_as_numeric_z3_ast(&(**right).expression);
                assert_eq!(lf, rf);
                unsafe {
                    if lf {
                        (
                            true,
                            z3_sys::Z3_mk_fpa_div(
                                self.z3_context,
                                self.nearest_even,
                                left_ast,
                                right_ast,
                            ),
                        )
                    } else {
                        (
                            false,
                            z3_sys::Z3_mk_div(self.z3_context, left_ast, right_ast),
                        )
                    }
                }
            }
            Expression::Mul { left, right } => {
                let (lf, left_ast) = self.get_as_numeric_z3_ast(&(**left).expression);
                let (rf, right_ast) = self.get_as_numeric_z3_ast(&(**right).expression);
                assert_eq!(lf, rf);
                unsafe {
                    if lf {
                        (
                            true,
                            z3_sys::Z3_mk_fpa_mul(
                                self.z3_context,
                                self.nearest_even,
                                left_ast,
                                right_ast,
                            ),
                        )
                    } else {
                        let tmp = vec![left_ast, right_ast];
                        (false, z3_sys::Z3_mk_mul(self.z3_context, 2, tmp.as_ptr()))
                    }
                }
            }
            Expression::Rem { left, right } => {
                let (lf, left_ast) = self.get_as_numeric_z3_ast(&(**left).expression);
                let (rf, right_ast) = self.get_as_numeric_z3_ast(&(**right).expression);
                assert_eq!(lf, rf);
                unsafe {
                    if lf {
                        (
                            true,
                            z3_sys::Z3_mk_fpa_rem(self.z3_context, left_ast, right_ast),
                        )
                    } else {
                        (
                            false,
                            z3_sys::Z3_mk_rem(self.z3_context, left_ast, right_ast),
                        )
                    }
                }
            }
            Expression::Sub { left, right } => {
                let (lf, left_ast) = self.get_as_numeric_z3_ast(&(**left).expression);
                let (rf, right_ast) = self.get_as_numeric_z3_ast(&(**right).expression);
                assert_eq!(lf, rf);
                unsafe {
                    if lf {
                        (
                            true,
                            z3_sys::Z3_mk_fpa_sub(
                                self.z3_context,
                                self.nearest_even,
                                left_ast,
                                right_ast,
                            ),
                        )
                    } else {
                        let tmp = vec![left_ast, right_ast];
                        (false, z3_sys::Z3_mk_sub(self.z3_context, 2, tmp.as_ptr()))
                    }
                }
            }
            Expression::And { .. }
            | Expression::Equals { .. }
            | Expression::GreaterOrEqual { .. }
            | Expression::GreaterThan { .. }
            | Expression::LessOrEqual { .. }
            | Expression::LessThan { .. }
            | Expression::Ne { .. }
            | Expression::Not { .. }
            | Expression::Or { .. } => {
                let ast = self.get_as_z3_ast(expression);
                unsafe {
                    (
                        false,
                        z3_sys::Z3_mk_ite(self.z3_context, ast, self.one, self.zero),
                    )
                }
            }
            Expression::BitAnd { .. }
            | Expression::BitOr { .. }
            | Expression::BitXor { .. }
            | Expression::Shl { .. }
            | Expression::Shr { .. } => {
                let ast = self.get_as_bv_z3_ast(expression, 128);
                unsafe { (false, z3_sys::Z3_mk_bv2int(self.z3_context, ast, false)) }
            }
            Expression::CompileTimeConstant(const_domain) => match const_domain {
                ConstantDomain::False => unsafe {
                    (false, z3_sys::Z3_mk_int(self.z3_context, 0, self.int_sort))
                },
                ConstantDomain::True => unsafe {
                    (false, z3_sys::Z3_mk_int(self.z3_context, 1, self.int_sort))
                },
                ConstantDomain::F32(..) | ConstantDomain::F64(..) => {
                    (true, self.get_as_z3_ast(expression))
                }
                _ => (false, self.get_as_z3_ast(expression)),
            },
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                let condition_ast = self.get_as_bool_z3_ast(&(**condition).expression);
                let (cf, consequent_ast) = self.get_as_numeric_z3_ast(&(**consequent).expression);
                let (af, alternate_ast) = self.get_as_numeric_z3_ast(&(**alternate).expression);
                assert_eq!(cf, af);
                unsafe {
                    (
                        cf,
                        z3_sys::Z3_mk_ite(
                            self.z3_context,
                            condition_ast,
                            consequent_ast,
                            alternate_ast,
                        ),
                    )
                }
            }
            Expression::Neg { operand } => {
                let (is_float, operand_ast) = self.get_as_numeric_z3_ast(&(**operand).expression);
                unsafe {
                    if is_float {
                        (true, z3_sys::Z3_mk_fpa_neg(self.z3_context, operand_ast))
                    } else {
                        (
                            false,
                            z3_sys::Z3_mk_unary_minus(self.z3_context, operand_ast),
                        )
                    }
                }
            }
            Expression::Reference(path) => {
                let path_str = CString::new(format!("&{:?}", path)).unwrap();
                unsafe {
                    let path_symbol =
                        z3_sys::Z3_mk_string_symbol(self.z3_context, path_str.into_raw());
                    (
                        false,
                        z3_sys::Z3_mk_const(self.z3_context, path_symbol, self.int_sort),
                    )
                }
            }
            Expression::Variable { path, var_type } => {
                use self::ExpressionType::*;
                match var_type {
                    Bool | NonPrimitive => {
                        let path_str = CString::new(format!("{:?}", path)).unwrap();
                        unsafe {
                            let path_symbol =
                                z3_sys::Z3_mk_string_symbol(self.z3_context, path_str.into_raw());
                            (
                                false,
                                z3_sys::Z3_mk_const(self.z3_context, path_symbol, self.int_sort),
                            )
                        }
                    }
                    F32 | F64 => (true, self.get_as_z3_ast(expression)),
                    _ => (false, self.get_as_z3_ast(expression)),
                }
            }
            Expression::Top => unsafe {
                (
                    false,
                    z3_sys::Z3_mk_fresh_const(self.z3_context, self.empty_str, self.int_sort),
                )
            },
            _ => (false, self.get_as_z3_ast(expression)),
        }
    }

    pub fn get_as_bool_z3_ast(&self, expression: &Expression) -> z3_sys::Z3_ast {
        match expression {
            Expression::BitAnd { .. } | Expression::BitOr { .. } | Expression::BitXor { .. } => {
                let bv = self.get_as_bv_z3_ast(expression, 128);
                unsafe {
                    let i = z3_sys::Z3_mk_bv2int(self.z3_context, bv, false);
                    let f = z3_sys::Z3_mk_eq(self.z3_context, i, self.zero);
                    z3_sys::Z3_mk_not(self.z3_context, f)
                }
            }
            Expression::CompileTimeConstant(const_domain) => match const_domain {
                ConstantDomain::False => unsafe { z3_sys::Z3_mk_false(self.z3_context) },
                ConstantDomain::True => unsafe { z3_sys::Z3_mk_true(self.z3_context) },
                _ => self.get_as_z3_ast(expression),
            },
            Expression::Top => unsafe {
                z3_sys::Z3_mk_fresh_const(self.z3_context, self.empty_str, self.bool_sort)
            },
            _ => self.get_as_z3_ast(expression),
        }
    }

    pub fn get_as_bv_z3_ast(&self, expression: &Expression, num_bits: u32) -> z3_sys::Z3_ast {
        match expression {
            Expression::And { .. }
            | Expression::Equals { .. }
            | Expression::GreaterOrEqual { .. }
            | Expression::GreaterThan { .. }
            | Expression::LessOrEqual { .. }
            | Expression::LessThan { .. }
            | Expression::Ne { .. }
            | Expression::Not { .. }
            | Expression::Or { .. } => {
                let ast = self.get_as_z3_ast(expression);
                // ast results in a boolean, but we want a bit vector.
                unsafe {
                    let bv_one = z3_sys::Z3_mk_int2bv(self.z3_context, num_bits, self.one);
                    let bv_zero = z3_sys::Z3_mk_int2bv(self.z3_context, num_bits, self.zero);
                    z3_sys::Z3_mk_ite(self.z3_context, ast, bv_one, bv_zero)
                }
            }
            Expression::BitAnd { left, right } => {
                let left_ast = self.get_as_bv_z3_ast(&(**left).expression, num_bits);
                let right_ast = self.get_as_bv_z3_ast(&(**right).expression, num_bits);
                unsafe { z3_sys::Z3_mk_bvand(self.z3_context, left_ast, right_ast) }
            }
            Expression::BitOr { left, right } => {
                let left_ast = self.get_as_bv_z3_ast(&(**left).expression, num_bits);
                let right_ast = self.get_as_bv_z3_ast(&(**right).expression, num_bits);
                unsafe { z3_sys::Z3_mk_bvor(self.z3_context, left_ast, right_ast) }
            }
            Expression::BitXor { left, right } => {
                let left_ast = self.get_as_bv_z3_ast(&(**left).expression, num_bits);
                let right_ast = self.get_as_bv_z3_ast(&(**right).expression, num_bits);
                unsafe { z3_sys::Z3_mk_bvxor(self.z3_context, left_ast, right_ast) }
            }
            Expression::CompileTimeConstant(..) => {
                let (f, num_ast) = self.get_as_numeric_z3_ast(expression);
                //todo: something about the previous call causes the path condition to become true
                // look into the way the path condition is propagated from the call.
                assert!(!f);
                unsafe { z3_sys::Z3_mk_int2bv(self.z3_context, num_bits, num_ast) }
            }
            Expression::ConditionalExpression {
                condition,
                consequent,
                alternate,
            } => {
                let condition_ast = self.get_as_bool_z3_ast(&(**condition).expression);
                let consequent_ast = self.get_as_bv_z3_ast(&(**consequent).expression, num_bits);
                let alternate_ast = self.get_as_bv_z3_ast(&(**alternate).expression, num_bits);
                unsafe {
                    z3_sys::Z3_mk_ite(
                        self.z3_context,
                        condition_ast,
                        consequent_ast,
                        alternate_ast,
                    )
                }
            }
            Expression::Shl { left, right } => {
                let left_ast = self.get_as_bv_z3_ast(&(**left).expression, num_bits);
                let right_ast = self.get_as_bv_z3_ast(&(**right).expression, num_bits);
                unsafe { z3_sys::Z3_mk_bvshl(self.z3_context, left_ast, right_ast) }
            }
            Expression::Shr {
                left,
                right,
                result_type,
            } => {
                let left_ast = self.get_as_bv_z3_ast(&(**left).expression, num_bits);
                let right_ast = self.get_as_bv_z3_ast(&(**right).expression, num_bits);
                unsafe {
                    if result_type.is_signed_integer() {
                        z3_sys::Z3_mk_bvashr(self.z3_context, left_ast, right_ast)
                    } else {
                        z3_sys::Z3_mk_bvlshr(self.z3_context, left_ast, right_ast)
                    }
                }
            }
            Expression::Variable { path, .. } => {
                let path_str = CString::new(format!("{:?}", path)).unwrap();
                unsafe {
                    let path_symbol =
                        z3_sys::Z3_mk_string_symbol(self.z3_context, path_str.into_raw());
                    let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
                    z3_sys::Z3_mk_const(self.z3_context, path_symbol, sort)
                }
            }
            Expression::Top => unsafe {
                let sort = z3_sys::Z3_mk_bv_sort(self.z3_context, num_bits);
                z3_sys::Z3_mk_fresh_const(self.z3_context, self.empty_str, sort)
            },
            _ => self.get_as_z3_ast(expression),
        }
    }
}
