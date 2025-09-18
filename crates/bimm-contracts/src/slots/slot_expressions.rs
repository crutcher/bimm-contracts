//! # Dimension Expressions.

use crate::math::maybe_iroot;
use core::fmt::{Display, Formatter};

/// A stack/static expression algebra for dimension sizes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SlotDimExpr<'a> {
    /// A parameter reference.
    Param {
        /// The id of the parameter.
        id: usize,
    },

    /// Negation of an expression.
    Negate {
        /// The child expression.
        child: &'a SlotDimExpr<'a>,
    },

    /// Exponentiation of an expression.
    Pow {
        /// The child expression.
        base: &'a SlotDimExpr<'a>,

        /// The exponent.
        exp: usize,
    },

    /// Sum of expressions.
    Sum {
        /// The child expressions.
        children: &'a [SlotDimExpr<'a>],
    },

    /// Product of expressions.
    Prod {
        /// The child expressions.
        children: &'a [SlotDimExpr<'a>],
    },
}

/// Display Adapter to format SlotDimExprs with a SlotIndex.
pub struct ExprDisplayAdapter<'a> {
    /// Slot index.
    pub index: &'a [&'a str],

    /// Expression to format.
    pub expr: &'a SlotDimExpr<'a>,
}

impl<'a> Display for ExprDisplayAdapter<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self.expr {
            SlotDimExpr::Param { id } => write!(f, "{}", self.index[*id]),
            SlotDimExpr::Negate { child } => write!(
                f,
                "(-{})",
                ExprDisplayAdapter {
                    expr: child,
                    index: self.index
                }
            ),
            SlotDimExpr::Pow { base: child, exp } => write!(
                f,
                "({}^{})",
                ExprDisplayAdapter {
                    expr: child,
                    index: self.index
                },
                exp
            ),
            SlotDimExpr::Sum { children } => {
                write!(f, "(")?;
                for (idx, expr) in children.iter().enumerate() {
                    if idx > 0 {
                        write!(f, "+")?;
                    }
                    write!(
                        f,
                        "{}",
                        ExprDisplayAdapter {
                            expr: expr,
                            index: self.index
                        }
                    )?;
                }
                write!(f, ")")
            }
            SlotDimExpr::Prod { children } => {
                write!(f, "(")?;
                for (idx, expr) in children.iter().enumerate() {
                    if idx > 0 {
                        write!(f, "*")?;
                    }
                    write!(
                        f,
                        "{}",
                        ExprDisplayAdapter {
                            expr: expr,
                            index: self.index
                        }
                    )?;
                }
                write!(f, ")")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum EvalResult {
    /// The evaluated value of the expression.
    Value { value: isize },

    /// The count of unbound parameters in the expression.
    UnboundParams {
        /// The count of unbound parameters.
        count: usize,
    },
}

/// Result of `SizeExpr::try_match()`.
///
/// All values are borrowed from the original expression,
/// so they are valid as long as the expression is valid.
///
/// Runtime errors (malformed expressions, too-many unbound parameters, etc.)
/// are not represented here; and are returned as `Err(String)` from `try_match`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatchResult {
    /// All params bound and expression equals target.
    Match,

    /// Expression value does not match the target.
    Conflict,

    /// Expression can be solved for a single unbound param.
    ParamConstraint {
        /// The id of the parameter.
        id: usize,

        /// The value the parameter must take to satisfy the expression.
        value: isize,
    },
}

impl<'a> SlotDimExpr<'a> {
    /// Evaluate an expression.
    ///
    /// ## Arguments
    ///
    /// - `env` - the binding environment.
    ///
    /// ## Returns
    ///
    /// A `TryEvalResult`:
    /// * `Value(value)` - the evaluated value of the expression.
    /// * `UnboundParams(count)` - the count of unbound parameters.
    #[must_use]
    fn try_eval(&self, env: &[Option<isize>]) -> EvalResult {
        #[inline(always)]
        fn reduce_children<'a>(
            exprs: &'a [SlotDimExpr<'a>],
            env: &[Option<isize>],
            zero: isize,
            op: fn(&mut isize, isize),
        ) -> EvalResult {
            let mut value = zero;
            let mut count = 0;
            for expr in exprs {
                match expr.try_eval(env) {
                    EvalResult::Value { value: v } => op(&mut value, v),
                    EvalResult::UnboundParams { count: c } => count += c,
                }
            }
            if count == 0 {
                EvalResult::Value { value }
            } else {
                EvalResult::UnboundParams { count }
            }
        }

        match self {
            SlotDimExpr::Param { id } => match env[*id] {
                Some(value) => EvalResult::Value { value: value },
                None => EvalResult::UnboundParams { count: 1 },
            },
            SlotDimExpr::Negate { child } => match child.try_eval(env) {
                EvalResult::Value { value } => EvalResult::Value { value: -value },
                x => x,
            },
            SlotDimExpr::Pow { base: child, exp } => match child.try_eval(env) {
                EvalResult::Value { value } => EvalResult::Value {
                    value: value.pow(*exp as u32),
                },
                x => x,
            },
            SlotDimExpr::Sum { children } => {
                reduce_children(children, env, 0, |tmp, value| *tmp += value)
            }
            SlotDimExpr::Prod { children } => {
                reduce_children(children, env, 1, |tmp, value| *tmp *= value)
            }
        }
    }

    /// Reconcile an expression against a target value.
    ///
    /// ## Arguments
    ///
    /// * `target`: The target value to match.
    /// * `env`: The environment containing bindings for parameters.
    ///
    /// ## Returns
    ///
    /// * `Ok(MatchResult::Match)` if the expression matches the target.
    /// * `Ok(MatchResult::MissMatch)` if the expression does not match the target.
    /// * `Ok(MatchResult::Constraint(name, value))` if the expression can be solved for a single unbound parameter.
    /// * `Ok(MatchResult::UnderConstrained)` if the expression cannot be solved with the current bindings.
    #[must_use]
    pub fn try_match(
        &self,
        target: isize,
        env: &[Option<isize>],
    ) -> Result<MatchResult, &'static str> {
        #[inline(always)]
        fn reduce_children<'a>(
            exprs: &'a [SlotDimExpr<'a>],
            env: &[Option<isize>],
            zero: isize,
            op: fn(&mut isize, isize),
        ) -> Result<(isize, Option<&'a SlotDimExpr<'a>>), &'static str> {
            let mut partial_value: isize = zero;
            let mut rem_expr = None;
            // At most one child can be unbound, and by only one parameter.
            for expr in exprs {
                match expr.try_eval(env) {
                    EvalResult::Value { value } => op(&mut partial_value, value),
                    EvalResult::UnboundParams { count } => {
                        if count == 1 && rem_expr.is_none() {
                            rem_expr = Some(expr);
                        } else {
                            return Err("Too many unbound params.");
                        }
                    }
                }
            }
            // If the monoid is fully bound, then return (value, None);
            // Otherwise, return (partial_value, expr).
            Ok((partial_value, rem_expr))
        }

        match self {
            SlotDimExpr::Param { id } => {
                let id = *id;
                if let Some(value) = env[id] {
                    if value == target {
                        Ok(MatchResult::Match)
                    } else {
                        Ok(MatchResult::Conflict)
                    }
                } else {
                    Ok(MatchResult::ParamConstraint { id, value: target })
                }
            }
            SlotDimExpr::Negate { child } => child.try_match(-target, env),
            SlotDimExpr::Pow { base: child, exp } => match maybe_iroot(target, *exp) {
                Some(root) => child.try_match(root, env),
                None => Err("No integer solution."),
            },
            SlotDimExpr::Sum { children } => {
                let (value, rem) = reduce_children(children, env, 0, |tmp, value| *tmp += value)?;
                if let Some(expr) = rem {
                    expr.try_match(target - value, env)
                } else if value == target {
                    Ok(MatchResult::Match)
                } else {
                    Ok(MatchResult::Conflict)
                }
            }
            SlotDimExpr::Prod { children } => {
                let (value, rem) = reduce_children(children, env, 1, |tmp, value| *tmp *= value)?;
                if let Some(expr) = rem {
                    if target % value != 0 {
                        // Non-integer solution
                        return Err("No integer solution.");
                    }
                    expr.try_match(target / value, env)
                } else if value == target {
                    Ok(MatchResult::Match)
                } else {
                    Ok(MatchResult::Conflict)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;
    use alloc::string::String;

    #[test]
    fn test_format() {
        static INDEX: [&str; 5] = ["a", "b", "c", "d", "e"];

        fn fmt(expr: &SlotDimExpr) -> String {
            format!(
                "{}",
                ExprDisplayAdapter {
                    expr: &expr,
                    index: &INDEX
                }
            )
        }

        assert_eq!(
            fmt(&SlotDimExpr::Param {
                id: INDEX
                    .iter()
                    .enumerate()
                    .find_map(|(i, k)| if *k == "a" { Some(i) } else { None })
                    .unwrap()
            }),
            "a"
        );

        let _expr = SlotDimExpr::Prod {
            children: &[
                SlotDimExpr::Param { id: 0 },
                SlotDimExpr::Param { id: 1 },
                SlotDimExpr::Sum {
                    children: &[
                        SlotDimExpr::Param { id: 2 },
                        SlotDimExpr::Pow {
                            base: &SlotDimExpr::Param { id: 3 },
                            exp: 2,
                        },
                        SlotDimExpr::Negate {
                            child: &SlotDimExpr::Param { id: 4 },
                        },
                    ],
                },
            ],
        };
        assert_eq!(fmt(&_expr), "(a*b*(c+(d^2)+(-e)))");
    }

    #[test]
    fn test_eval_param() {
        let env = [Some(5), None];

        let expr = SlotDimExpr::Param { id: 0 };
        assert_eq!(expr.try_eval(&env), EvalResult::Value { value: 5 });
        assert_eq!(expr.try_match(5, &env), Ok(MatchResult::Match));
        assert_eq!(expr.try_match(42, &env), Ok(MatchResult::Conflict));

        let expr = SlotDimExpr::Param { id: 1 };
        assert_eq!(expr.try_eval(&env), EvalResult::UnboundParams { count: 1 });
        assert_eq!(
            expr.try_match(5, &env),
            Ok(MatchResult::ParamConstraint { id: 1, value: 5 })
        );
    }

    #[test]
    fn try_eval_negate() {
        let expr = SlotDimExpr::Negate {
            child: &SlotDimExpr::Param { id: 0 },
        };

        let env = [Some(5)];
        assert_eq!(expr.try_eval(&env), EvalResult::Value { value: -5 });
        assert_eq!(expr.try_match(-5, &env), Ok(MatchResult::Match));
        assert_eq!(expr.try_match(42, &env), Ok(MatchResult::Conflict));

        let env = [None];
        assert_eq!(expr.try_eval(&env), EvalResult::UnboundParams { count: 1 });
        assert_eq!(
            expr.try_match(-5, &env),
            Ok(MatchResult::ParamConstraint { id: 0, value: 5 })
        );
    }

    #[test]
    fn try_eval_pow() {
        let expr = SlotDimExpr::Pow {
            base: &SlotDimExpr::Param { id: 0 },
            exp: 3,
        };

        let env = [Some(5)];
        assert_eq!(expr.try_eval(&env), EvalResult::Value { value: 125 });
        assert_eq!(expr.try_match(125, &env), Ok(MatchResult::Match));
        assert_eq!(expr.try_match(42, &env), Err("No integer solution."));

        let env = [None];
        assert_eq!(expr.try_eval(&env), EvalResult::UnboundParams { count: 1 });
        assert_eq!(
            expr.try_match(125, &env),
            Ok(MatchResult::ParamConstraint { id: 0, value: 5 })
        );
    }

    #[test]
    fn test_eval_sum() {
        let expr = SlotDimExpr::Sum {
            children: &[
                SlotDimExpr::Param { id: 0 },
                SlotDimExpr::Param { id: 1 },
                SlotDimExpr::Param { id: 2 },
                SlotDimExpr::Param { id: 3 },
            ],
        };

        let env = [Some(2), Some(3), Some(4), Some(5)];
        assert_eq!(expr.try_eval(&env), EvalResult::Value { value: 14 });
        assert_eq!(expr.try_match(14, &env), Ok(MatchResult::Match));
        assert_eq!(expr.try_match(42, &env), Ok(MatchResult::Conflict));

        let env = [Some(2), Some(3), None, Some(5)];
        assert_eq!(expr.try_eval(&env), EvalResult::UnboundParams { count: 1 });
        assert_eq!(
            expr.try_match(14, &env),
            Ok(MatchResult::ParamConstraint { id: 2, value: 4 })
        );

        let env = [Some(5), Some(3), None, None];
        assert_eq!(expr.try_eval(&env), EvalResult::UnboundParams { count: 2 });
        assert_eq!(expr.try_match(14, &env), Err("Too many unbound params."));
    }

    #[test]
    fn test_eval_prod() {
        let expr = SlotDimExpr::Prod {
            children: &[
                SlotDimExpr::Param { id: 0 },
                SlotDimExpr::Param { id: 1 },
                SlotDimExpr::Param { id: 2 },
                SlotDimExpr::Param { id: 3 },
            ],
        };

        let env = [Some(2), Some(3), Some(4), Some(5)];
        assert_eq!(expr.try_eval(&env), EvalResult::Value { value: 120 });
        assert_eq!(expr.try_match(120, &env), Ok(MatchResult::Match));
        assert_eq!(expr.try_match(42, &env), Ok(MatchResult::Conflict));

        let env = [Some(2), Some(3), None, Some(5)];
        assert_eq!(expr.try_eval(&env), EvalResult::UnboundParams { count: 1 });
        assert_eq!(
            expr.try_match(120, &env),
            Ok(MatchResult::ParamConstraint { id: 2, value: 4 })
        );

        let env = [Some(1), Some(5), None, Some(5)];
        assert_eq!(expr.try_match(40, &env), Err("No integer solution."));

        let env = [Some(5), Some(3), None, None];
        assert_eq!(expr.try_eval(&env), EvalResult::UnboundParams { count: 2 });
        assert_eq!(expr.try_match(120, &env), Err("Too many unbound params."));
    }
}
