//! Burn Framework Support

use crate::ShapeArgument;
use alloc::vec::Vec;
use tch::{Shape, Tensor};

impl ShapeArgument for Tensor {
    fn get_shape_vec(self) -> Vec<usize> {
        self.shape()
            .to_vec()
            .into_iter()
            .map(|x| x.to_usize())
            .collect()
    }
}

impl ShapeArgument for T
where
    T: Shape,
{
    fn get_shape_vec(self) -> Vec<usize> {
        self.to_shape().as_ref().to_vec()
    }
}
