### [bimm-contracts](crates/bimm-contracts) - a crate for static shape contracts for tensors.

[![Coverage Status](https://coveralls.io/repos/github/crutcher/bimm-contracts/badge.svg?branch=main)](https://coveralls.io/github/crutcher/bimm-contracts?branch=main)
[![Crates.io Version](https://img.shields.io/crates/v/bimm-contracts)](https://crates.io/crates/bimm-contracts)
[![docs.rs](https://img.shields.io/docsrs/bimm-contracts)](https://docs.rs/bimm-contracts/latest/bimm-contracts/)

Developed as part of the [bimm - burn image models](https://github.com/crutcher/bimm) suite.

This crate provides a stand-alone library for defining and enforcing tensor shape contracts
in-line with the Burn framework modules and methods.

This includes:
- A macro for defining shape contracts.
- static shape contracts.
- stack-checked (minimizing heap usage) shape assertions.
- an interface for unpacking tensor shapes into their components,
  allowing for parameterized dimensions; and nice error messages
  when the shape does not match the contract.
- a macro for running shape checks periodically,
  amortizing the cost of checks over multiple calls.

```rust
use bimm_contracts::{unpack_shape_contract, shape_contract, run_periodically};

pub fn window_partition<B: Backend, K>(
    tensor: Tensor<B, 4, K>,
    window_size: usize,
) -> Tensor<B, 4, K>
where
    K: BasicOps<B>,
{
    let [b, h_wins, w_wins, c] = unpack_shape_contract!(
        [
            "batch",
            "height" = "h_wins" * "window_size",
            "width" = "w_wins" * "window_size",
            "channels"
        ],
        &tensor,
        &["batch", "h_wins", "w_wins", "channels"],
        &[("window_size", window_size)],
    );

    let tensor = tensor
        .reshape([b, h_wins, window_size, w_wins, window_size, c])
        .swap_dims(2, 3)
        .reshape([b * h_wins * w_wins, window_size, window_size, c]);

    // Run an amortized check on the output shape.
    //
    // `run_periodically!{}` runs the first 10 times,
    // then on an incrementally lengthening schedule,
    // until it reaches its default period of 1000.
    //
    // Due to amortization, in release builds, this averages ~4ns:
    assert_shape_contract_periodically!(
        [
            "batch" * "h_wins" * "w_wins",
            "window_size",
            "window_size",
            "channels"
        ],
        &tensor,
        &[
            ("batch", b),
            ("h_wins", h_wins),
            ("w_wins", w_wins),
            ("window_size", window_size),
            ("channels", c),
        ]
    );
    
    tensor
}
```

## Contributing

See the [CONTRIBUTING](CONTRIBUTING.md) guide for build and contribution instructions.
