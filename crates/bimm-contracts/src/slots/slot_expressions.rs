//! # Dimension Expressions.

use crate::math::maybe_iroot;
use crate::slots::slot_map::SlotBindings;
use alloc::string::{String, ToString};
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

impl SlotDimExpr<'_> {
    /// Format an expression with a slot map.
    pub fn format(&self, f: &mut Formatter<'_>, index: &[&str]) -> core::fmt::Result {
        DisplayAdapter { expr: self, index }.fmt(f)
    }
}

/// Display Adapter to format SlotDimExprs with a SlotIndex.
pub struct DisplayAdapter<'a> {
    expr: &'a SlotDimExpr<'a>,
    index: &'a [&'a str],
}

impl<'a> Display for DisplayAdapter<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self.expr {
            SlotDimExpr::Param { id } => write!(f, "{}", self.index[*id]),
            SlotDimExpr::Negate { child } => write!(
                f,
                "(-{})",
                DisplayAdapter {
                    expr: child,
                    index: self.index
                }
            ),
            SlotDimExpr::Pow { base: child, exp } => write!(
                f,
                "({}^{})",
                DisplayAdapter {
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
                        DisplayAdapter {
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
                        DisplayAdapter {
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
    fn try_eval<E>(&self, env: &E) -> EvalResult
    where
        E: SlotBindings,
    {
        #[inline(always)]
        fn reduce_children<'a, E>(
            exprs: &'a [SlotDimExpr<'a>],
            env: &E,
            zero: isize,
            op: fn(&mut isize, isize),
        ) -> EvalResult
        where
            E: SlotBindings,
        {
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
            SlotDimExpr::Param { id } => match env.get_slot(*id) {
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
    pub fn try_match<E>(&self, target: isize, env: &E) -> Result<MatchResult, String>
    where
        E: SlotBindings,
    {
        #[inline(always)]
        fn reduce_children<'a, E>(
            exprs: &'a [SlotDimExpr<'a>],
            env: &E,
            zero: isize,
            op: fn(&mut isize, isize),
        ) -> Result<(isize, Option<&'a SlotDimExpr<'a>>), String>
        where
            E: SlotBindings,
        {
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
                            return Err("Too many unbound params".to_string());
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
                if let Some(value) = env.get_slot(id) {
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
                None => Err("No integer solution.".to_string()),
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
                        return Err("No integer solution.".to_string());
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
    use crate::slots::slot_map::SlotIndex;
    use alloc::format;
    use alloc::string::String;

    #[test]
    fn test_format() {
        static INDEX: SlotIndex = SlotIndex {
            keys: &["a", "b", "c"],
        };

        fn fmt(expr: &SlotDimExpr) -> String {
            format!(
                "{}",
                DisplayAdapter {
                    expr: &expr,
                    index: &INDEX.keys
                }
            )
        }

        assert_eq!(
            fmt(&SlotDimExpr::Param {
                id: INDEX.slot("a")
            }),
            "a"
        );
    }

    #[test]
    fn test_too_many_unbound_params() {
        let env = [Some(5), Some(3), None, None];
        let expr = SlotDimExpr::Sum {
            children: &[
                SlotDimExpr::Param { id: 0 },
                SlotDimExpr::Param { id: 1 },
                SlotDimExpr::Param { id: 2 },
                SlotDimExpr::Param { id: 3 },
            ],
        };
        assert_eq!(expr.try_eval(&env), EvalResult::UnboundParams { count: 2 });
    }

    #[test]
    fn test_pow_no_integer_solution() {
        let env = [Some(5)];

        let expr = SlotDimExpr::Pow {
            base: &SlotDimExpr::Param { id: 0 },
            exp: 3,
        };

        assert_eq!(expr.try_eval(&env), EvalResult::Value { value: 125 });
        assert!(expr.try_match(126, &env).is_err());
    }

    #[test]
    fn test_prod_no_integer_solution() {
        let env = [Some(5), None];

        let expr = SlotDimExpr::Prod {
            children: &[SlotDimExpr::Param { id: 0 }, SlotDimExpr::Param { id: 1 }],
        };
        assert_eq!(expr.try_eval(&env), EvalResult::UnboundParams { count: 1 });
    }
}
