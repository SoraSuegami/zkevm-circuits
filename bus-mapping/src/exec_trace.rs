//! This module contains the logic for parsing and interacting with EVM
//! execution traces.
pub(crate) mod exec_step;
pub(crate) mod parsing;
use crate::evm::EvmWord;
use crate::operation::{container::OperationContainer, Operation};
use crate::operation::{MemoryOp, StackOp, StorageOp, Target};
use crate::Error;
use core::ops::{Index, IndexMut};
pub use exec_step::ExecutionStep;
use num::BigUint;
pub(crate) use parsing::ParsedExecutionStep;
use pasta_curves::arithmetic::FieldExt;
use serde::Serialize;
use std::convert::TryFrom;

/// Definition of all of the constants related to an Ethereum block and
/// therefore, related with an [`ExecutionTrace`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct BlockConstants<F: FieldExt> {
    hash: EvmWord, // Until we know how to deal with it
    #[serde(serialize_with = "serialize_fp")]
    coinbase: F,
    #[serde(serialize_with = "serialize_fp")]
    timestamp: F,
    #[serde(serialize_with = "serialize_fp")]
    number: F,
    #[serde(serialize_with = "serialize_fp")]
    difficulty: F,
    #[serde(serialize_with = "serialize_fp")]
    gas_limit: F,
    #[serde(serialize_with = "serialize_fp")]
    chain_id: F,
    #[serde(serialize_with = "serialize_fp")]
    base_fee: F,
}

fn serialize_fp<S, F>(v: &F, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
    F: FieldExt,
{
    serializer
        .serialize_str(&BigUint::from_bytes_le(&v.to_bytes()).to_str_radix(10))
}

impl<F: FieldExt> BlockConstants<F> {
    #[allow(clippy::too_many_arguments)]
    /// Generates a new `BlockConstants` instance from it's fields.
    pub fn new(
        hash: EvmWord,
        coinbase: F,
        timestamp: F,
        number: F,
        difficulty: F,
        gas_limit: F,
        chain_id: F,
        base_fee: F,
    ) -> BlockConstants<F> {
        BlockConstants {
            hash,
            coinbase,
            timestamp,
            number,
            difficulty,
            gas_limit,
            chain_id,
            base_fee,
        }
    }
    #[inline]
    /// Return the hash of a block.
    pub fn hash(&self) -> &EvmWord {
        &self.hash
    }

    #[inline]
    /// Return the coinbase of a block.
    pub fn coinbase(&self) -> &F {
        &self.coinbase
    }

    #[inline]
    /// Return the timestamp of a block.
    pub fn timestamp(&self) -> &F {
        &self.timestamp
    }

    #[inline]
    /// Return the block number.
    pub fn number(&self) -> &F {
        &self.number
    }

    #[inline]
    /// Return the difficulty of a block.
    pub fn difficulty(&self) -> &F {
        &self.difficulty
    }

    #[inline]
    /// Return the gas_limit of a block.
    pub fn gas_limit(&self) -> &F {
        &self.gas_limit
    }

    #[inline]
    /// Set the gas_limit of a block.
    pub fn set_gas_limit(&mut self, new_gas_limit: F) {
        self.gas_limit = new_gas_limit;
    }

    #[inline]
    /// Return the chain ID associated to a block.
    pub fn chain_id(&self) -> &F {
        &self.chain_id
    }

    #[inline]
    /// Return the base fee of a block.
    pub fn base_fee(&self) -> &F {
        &self.base_fee
    }
}

/// Result of the parsing of an EVM execution trace.
/// This structure is the centre of the crate and is intended to be the only
/// entry point to it. The `ExecutionTrace` provides three main actions:
///
/// 1. Generate an `ExecutionTrace` instance by parsing an EVM trace (JSON
/// format for now).
///
/// 2. Generate and provide an iterator over all of the
/// [`ExecutionStep`]s giving an easy way to witness all of the data of each
/// step when building the Circuits for the EVM Proof.
///
/// 3. Generate and provide an ordered list of all of the
/// [`StackOp`]s,
/// [`MemoryOp`]s and
/// [`StorageOp`](crate::operation::StorageOp)s that each
/// [`OpcodeId`](crate::evm::OpcodeId)s used in each `ExecutionTrace` step so that
/// the State Proof witnesses are already generated on a structured manner and
/// ready to be added into the State circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecutionTrace<F: FieldExt> {
    steps: Vec<ExecutionStep>,
    block_ctants: BlockConstants<F>,
    container: OperationContainer,
}

impl<F: FieldExt> Index<usize> for ExecutionTrace<F> {
    type Output = ExecutionStep;
    fn index(&self, index: usize) -> &Self::Output {
        &self.steps[index]
    }
}

impl<F: FieldExt> IndexMut<usize> for ExecutionTrace<F> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.steps[index]
    }
}

impl<F: FieldExt> ExecutionTrace<F> {
    /// Given an EVM trace in JSON format according to the specs and format
    /// shown in [zkevm-test-vectors crate](https://github.com/appliedzkp/zkevm-testing-vectors),
    /// generate the execution steps.
    pub fn load_execution_steps<T: AsRef<[u8]>>(
        bytes: T,
    ) -> Result<Vec<ExecutionStep>, Error> {
        serde_json::from_slice::<Vec<ParsedExecutionStep>>(bytes.as_ref())
            .map_err(|_| Error::SerdeError)?
            .iter()
            .map(ExecutionStep::try_from)
            .collect::<Result<Vec<ExecutionStep>, Error>>()
    }

    /// Given an EVM trace in JSON format according to the specs and format
    /// shown in [zkevm-test-vectors crate](https://github.com/appliedzkp/zkevm-testing-vectors), generate an `ExecutionTrace`
    /// and generate all of the [`Operation`]s associated to each one of it's
    /// [`ExecutionStep`]s filling them bus-mapping instances.
    pub fn from_trace_bytes<T: AsRef<[u8]>>(
        bytes: T,
        block_ctants: BlockConstants<F>,
    ) -> Result<ExecutionTrace<F>, Error> {
        let trace_loaded = Self::load_execution_steps(bytes)?;
        ExecutionTrace::<F>::new(trace_loaded, block_ctants)
    }

    /// Given a vector of [`ExecutionStep`]s and a [`BlockConstants`] instance,
    /// generate an [`ExecutionTrace`] by:
    ///
    /// 1) Setting the correct [`GlobalCounter`](crate::evm::GlobalCounter) to
    /// each [`ExecutionStep`].
    /// 2) Generating the corresponding [`Operation`]s, registering them in the
    /// container and storing the [`OperationRef`]s to each one of the
    /// generated ops into the bus-mapping instances of each [`ExecutionStep`].
    pub(crate) fn new(
        steps: Vec<ExecutionStep>,
        block_ctants: BlockConstants<F>,
    ) -> Result<Self, Error> {
        ExecutionTrace {
            steps,
            block_ctants,
            /// Dummy empty container to enable build.
            container: OperationContainer::new(),
        }
        .build()
    }

    /// Returns an ordered `Vec` containing all the [`StackOp`]s of the actual
    /// `ExecutionTrace` so that they can be directly included in the State
    /// proof.
    pub fn sorted_stack_ops(&self) -> Vec<StackOp> {
        self.container.sorted_stack()
    }

    /// Returns an ordered `Vec` containing all the [`MemoryOp`]s of the actual
    /// `ExecutionTrace` so that they can be directly included in the State
    /// proof.
    pub fn sorted_memory_ops(&self) -> Vec<MemoryOp> {
        self.container.sorted_memory()
    }

    /// Returns an ordered `Vec` containing all the [`StorageOp`]s of the actual
    /// `ExecutionTrace` so that they can be directly included in the State
    /// proof.
    pub fn sorted_storage_ops(&self) -> Vec<StorageOp> {
        self.container.sorted_storage()
    }

    /// Traverses the trace step by step, and for each [`ExecutionStep`]:
    /// 1.  Sets the correct [`GlobalCounter`](crate::evm::GlobalCounter).
    /// 2.  Generates the corresponding [`Operation`]s  associated to the
    /// [`OpcodeId`](crate::evm::OpcodeId) executed in the step and stores them inside the
    /// [`OperationContainer`] instance stored inside of the trace.
    /// It also adds the [`OperationRef`]s obtained from the container
    /// addition into each [`ExecutionStep`] bus-mapping instances.
    fn build(mut self) -> Result<Self, Error> {
        // Set a counter to add the correct global counters.
        let mut gc = 0usize;
        let mut new_container = OperationContainer::new();
        // XXX: We need a better achitecture to work on that without cloning..
        let cloned_steps = self.steps().clone();

        // Generate operations and update the GlobalCounter of each step.
        self.steps_mut().iter_mut().enumerate().try_for_each(
            |(idx, exec_step)| {
                // Set correct global counter
                exec_step.set_gc(gc);
                // Add the `OpcodeId` associated ops and increment the gc counting
                // all of them.
                gc += exec_step.gen_associated_ops(
                    &mut new_container,
                    &cloned_steps[idx + 1..],
                )?;
                // Sum 1 to counter so that we set the next exec_step GC to the
                // correct index
                //gc += 1;
                Ok(())
            },
        )?;
        // Replace the empty original container with the new one we just filled.
        self.container = new_container;
        Ok(self)
    }

    /// Registers an [`Operation`] into the [`OperationContainer`] and then adds
    /// a reference to the stored operation ([`OperationRef`]) inside the
    /// bus-mapping instance of the [`ExecutionStep`] located at `exec_step_idx`
    /// inside the [`ExecutionTrace`].
    pub(crate) fn add_op_to_container(
        &mut self,
        op: Operation,
        exec_step_idx: usize,
    ) {
        let op_ref = self.container_mut().insert(op);
        self.steps[exec_step_idx]
            .bus_mapping_instance_mut()
            .push(op_ref);
    }

    /// Returns a reference to the [`ExecutionStep`] vector instance
    /// that the `ExecutionTrace` holds.
    pub fn steps(&self) -> &Vec<ExecutionStep> {
        &self.steps
    }

    /// Returns a mutable reference to the [`ExecutionStep`] vector instance
    /// that the `ExecutionTrace` holds.
    fn steps_mut(&mut self) -> &mut Vec<ExecutionStep> {
        &mut self.steps
    }

    /// Returns a reference to the [`ExecutionStep`] vector instance
    /// that the `ExecutionTrace` holds.
    pub fn ops(&self) -> &OperationContainer {
        &self.container
    }

    /// Returns a mutable reference to the [`OperationContainer`] instance that
    /// the `ExecutionTrace` holds.
    fn container_mut(&mut self) -> &mut OperationContainer {
        &mut self.container
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// The target and index of an `Operation` in the context of an
/// `ExecutionTrace`.
pub struct OperationRef(Target, usize);

impl From<(Target, usize)> for OperationRef {
    fn from(op_ref_data: (Target, usize)) -> Self {
        match op_ref_data.0 {
            Target::Memory => Self(Target::Memory, op_ref_data.1),
            Target::Stack => Self(Target::Stack, op_ref_data.1),
            Target::Storage => Self(Target::Storage, op_ref_data.1),
            _ => unreachable!(),
        }
    }
}

impl OperationRef {
    /// Return the `OperationRef` as a `usize`.
    pub const fn as_usize(&self) -> usize {
        self.1
    }

    /// Return the [`Target`] op type of the `OperationRef`.
    pub const fn target(&self) -> Target {
        self.0
    }
}

#[cfg(test)]
mod trace_tests {
    use super::*;
    use crate::evm::Stack;
    use crate::{
        bytecode,
        bytecode::Bytecode,
        evm::{
            opcodes::ids::OpcodeId, GasCost, GasInfo, GlobalCounter,
            ProgramCounter, StackAddress,
        },
        exec_trace::ExecutionStep,
        operation::{StackOp, RW},
    };

    macro_rules! gas_info {
        ($gas:ident, $gas_cost: ident) => {{
            GasInfo {
                gas: {
                    let temp = $gas;
                    $gas -= GasCost::$gas_cost.as_usize() as u64;
                    temp
                },
                gas_cost: GasCost::$gas_cost,
            }
        }};
    }

    #[test]
    fn exec_trace_parsing() {
        let code = bytecode! {
            // Setup memory
            PUSH1 0x80u64;
            PUSH1 0x40u64;
            MSTORE;

            // Start byte code tested
            [start]
            PUSH1 0x40u64;
            MLOAD;
        };

        let mut block_ctants = BlockConstants::new(
            EvmWord::from(0u8),
            pasta_curves::Fp::from_u64(0xc014ba5eu64),
            pasta_curves::Fp::from_u64(1633398551u64),
            pasta_curves::Fp::from_u64(123456u64),
            pasta_curves::Fp::from_u64(0x200000u64),
            pasta_curves::Fp::from_u64(100u64),
            pasta_curves::Fp::one(),
            pasta_curves::Fp::from_u64(97u64),
        );

        // Get the execution steps from geth
        let steps = &ExecutionTrace::<pasta_curves::Fp>::load_execution_steps(
            geth_utils::trace(
                &serde_json::to_string(&block_ctants).unwrap(),
                code.to_bytes(),
            )
            .unwrap()
            .as_bytes(),
        )
        .unwrap()[code.get_pos("start")..];

        // Start from the same gas limit for the simulation
        let mut gas = steps[0].gas_info().gas;
        block_ctants.set_gas_limit(pasta_curves::Fp::from_u64(gas as u64));

        // Obtained trace computation
        let obtained_exec_trace = ExecutionTrace::<pasta_curves::Fp>::new(
            steps.to_vec(),
            block_ctants.clone(),
        )
        .expect("Error on trace generation");

        // Generate the expected ExecutionTrace corresponding to the JSON
        // provided above.

        // Container is shared across ExecutionSteps
        let mut container = OperationContainer::new();

        // The memory is the same in both steps as none of them touches the
        // memory of the EVM.
        let mem_map = steps[0].memory.clone();

        // Generate Step1 corresponding to PUSH1 40

        let mut step_1 = ExecutionStep {
            memory: mem_map.clone(),
            stack: Stack::empty(),
            instruction: OpcodeId::PUSH1,
            gas_info: gas_info!(gas, FASTEST),
            depth: 1u8,
            pc: ProgramCounter::from(5),
            gc: GlobalCounter::from(0),
            bus_mapping_instance: vec![],
        };

        // Add StackOp associated to the 0x40 pushed to the Stack
        step_1
            .bus_mapping_instance_mut()
            .push(container.insert(StackOp::new(
                RW::WRITE,
                GlobalCounter(1usize),
                StackAddress::from(1023),
                EvmWord::from(0x40u8),
            )));

        // Generate Step2 corresponding to MLOAD
        let mut step_2 = ExecutionStep {
            memory: mem_map.clone(),
            stack: Stack(vec![EvmWord::from(0x40u8)]),
            instruction: OpcodeId::MLOAD,
            gas_info: gas_info!(gas, FASTEST),
            depth: 1u8,
            pc: ProgramCounter::from(7),
            gc: GlobalCounter::from(1),
            bus_mapping_instance: vec![],
        };

        // Add StackOp associated to the read of `offset`
        step_2
            .bus_mapping_instance_mut()
            .push(container.insert(StackOp::new(
                RW::READ,
                GlobalCounter(2usize),
                StackAddress::from(1023),
                EvmWord::from(0x40u8),
            )));

        // Add MemoryOp associated to the read of an `EvmWord` at position `offset - offset+32`
        step_2.bus_mapping_instance_mut().push(container.insert(
            MemoryOp::new(
                RW::READ,
                GlobalCounter(3usize),
                0x40.into(),
                EvmWord::from(0x80u8),
            ),
        ));

        // Add StackOp associated to the write of the previous memory read value at the position where offset was.
        step_2
            .bus_mapping_instance_mut()
            .push(container.insert(StackOp::new(
                RW::WRITE,
                GlobalCounter(4usize),
                StackAddress::from(1023),
                EvmWord::from(0x80u8),
            )));

        // Generate Step3 corresponding to STOP
        let step_3 = ExecutionStep {
            memory: mem_map,
            stack: Stack(vec![EvmWord::from(0x80u8)]),
            instruction: OpcodeId::STOP,
            gas_info: GasInfo {
                gas,
                gas_cost: GasCost::from(0u8),
            },
            depth: 1u8,
            pc: ProgramCounter::from(8),
            gc: GlobalCounter::from(4),
            bus_mapping_instance: vec![],
        };

        let expected_exec_trace = ExecutionTrace {
            steps: vec![step_1, step_2, step_3],
            block_ctants: block_ctants.clone(),
            container,
        };

        assert_eq!(obtained_exec_trace, expected_exec_trace)
    }
}
