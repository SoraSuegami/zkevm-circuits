use crate::sha256_circuit::util::*;
use crate::{
    evm_circuit::util::{constraint_builder::BaseConstraintBuilder, not, rlc},
    table::KeccakTable,
    util::Expr,
};
use eth_types::Field;
use gadgets::util::{and, select, sum, xor};
use halo2_proofs::plonk::Instance;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use log::{debug, info};
use std::{env::var, marker::PhantomData, vec};

#[derive(Clone, Debug, PartialEq)]
struct ShaRow<F> {
    w: [bool; NUM_BITS_PER_WORD_W],
    a: [bool; NUM_BITS_PER_WORD_EXT],
    e: [bool; NUM_BITS_PER_WORD_EXT],
    is_final: bool,
    is_dummy: bool,
    length: usize,
    // data_rlc: F,
    // hash_rlc: F,
    is_paddings: [bool; ABSORB_WIDTH_PER_ROW_BYTES],
    // data_rlcs: [F; ABSORB_WIDTH_PER_ROW_BYTES],
    input_word: F,
    output_word: F,
}

/// Configuration for [`Sha256BitChip`].
#[derive(Clone, Debug)]
pub struct Sha256BitConfig<F> {
    q_enable: Column<Fixed>,
    q_first: Column<Fixed>,
    q_extend: Column<Fixed>,
    pub q_start: Column<Fixed>,
    q_compression: Column<Fixed>,
    q_end: Column<Fixed>,
    q_padding: Column<Fixed>,
    q_padding_last: Column<Fixed>,
    q_squeeze: Column<Fixed>,
    word_w: [Column<Advice>; NUM_BITS_PER_WORD_W],
    word_a: [Column<Advice>; NUM_BITS_PER_WORD_EXT],
    word_e: [Column<Advice>; NUM_BITS_PER_WORD_EXT],
    is_final: Column<Advice>,
    is_paddings: [Column<Advice>; ABSORB_WIDTH_PER_ROW_BYTES],
    is_dummy: Column<Advice>,
    // data_rlcs: [Column<Advice>; ABSORB_WIDTH_PER_ROW_BYTES],
    round_cst: Column<Fixed>,
    h_a: Column<Fixed>,
    h_e: Column<Fixed>,
    /// The columns for other circuits to lookup hash results
    /// Byte array input length
    pub input_len: Column<Advice>,
    /// The input words (16 bytes) result,
    pub input_words: Column<Advice>,
    /// The enable flag of the output hash.
    pub is_output_enabled: Column<Advice>,
    /// The hash words (8 bytes) result,
    pub output_words: Column<Advice>,
    /// The column for the randomness used to compute random linear
    /// combinations.
    //pub randomness: Column<Advice>,
    _marker: PhantomData<F>,
}

/// Chip for the SHA256 hash function.
#[derive(Clone, Debug)]
pub struct Sha256BitChip<F: Field> {
    config: Sha256BitConfig<F>,
    max_input_len: usize,
}

#[derive(Clone, Debug)]
pub struct Sha256AssignedRow<F: Field> {
    pub offset: usize,
    pub q_start: AssignedCell<F, F>,
    pub input_len: AssignedCell<F, F>,
    pub input_word: AssignedCell<F, F>,
    pub is_output_enabled: AssignedCell<F, F>,
    pub output_word: AssignedCell<F, F>,
}

// impl<F: Field> Sha256BitChip<F> {
//     fn r() -> F {
//         F::from(123456)
//     }
// }

impl<F: Field> Sha256BitChip<F> {
    /// Create a new [`Sha256BitChip`] from the configuration.
    ///
    /// # Arguments
    /// * config - a configuration for [`Sha256BitChip`].
    ///
    /// # Return values
    /// Returns a new [`Sha256BitChip`]
    pub fn new(config: Sha256BitConfig<F>, max_input_len: usize) -> Self {
        assert_eq!(max_input_len % 64, 0);
        Sha256BitChip {
            config,
            max_input_len,
        }
    }

    /*/// The number of sha256 permutations that can be done in this circuit
    pub fn capacity(&self) -> usize {
        // Subtract one for unusable rows
        self.size / (NUM_ROUNDS + 8) - 1
    }*/

    /// Given the input, returns a vector of the assigned cells for the hash
    /// results.
    ///
    /// # Arguments
    /// * layouter - a layouter of the constraints system.
    /// * inputs - a vector of input bytes.
    ///
    /// # Return values
    /// Returns a vector of the assigned cells for the hash results.
    pub fn digest(
        &self,
        region: &mut Region<'_, F>,
        input: &[u8],
    ) -> Result<Vec<Sha256AssignedRow<F>>, Error> {
        assert!(input.len() <= self.max_input_len);
        let witness = sha256(input, self.max_input_len);
        self.config.assign(region, &witness)
    }
}

impl<F: Field> Sha256BitConfig<F> {
    /// Configure constraints for [`Sha256BitChip`]
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        //let r = Sha256BitChip::r();
        let q_enable = meta.fixed_column();
        let q_first = meta.fixed_column();
        let q_extend = meta.fixed_column();
        let q_start = meta.fixed_column();
        meta.enable_equality(q_start);
        let q_compression = meta.fixed_column();
        let q_end = meta.fixed_column();
        let q_padding = meta.fixed_column();
        let q_padding_last = meta.fixed_column();
        let q_squeeze = meta.fixed_column();
        let word_w = array_init::array_init(|_| meta.advice_column());
        let word_a = array_init::array_init(|_| meta.advice_column());
        let word_e = array_init::array_init(|_| meta.advice_column());
        let is_final = meta.advice_column();
        let is_paddings = array_init::array_init(|_| meta.advice_column());
        let is_dummy = meta.advice_column();
        // let data_rlcs = array_init::array_init(|_| meta.advice_column());
        let round_cst = meta.fixed_column();
        let h_a = meta.fixed_column();
        let h_e = meta.fixed_column();
        //let hash_table = KeccakTable::construct(meta);
        // let randomness = meta.advice_column();
        // meta.enable_equality(randomness);
        let input_len = meta.advice_column();
        meta.enable_equality(input_len);
        let input_words = meta.advice_column();
        meta.enable_equality(input_words);
        let is_output_enabled = meta.advice_column();
        meta.enable_equality(is_output_enabled);
        let output_words = meta.advice_column();
        meta.enable_equality(output_words);
        // let data_rlc = hash_table.input_rlc;
        // let hash_rlc = hash_table.output_rlc;
        // let final_hash_bytes = array_init::array_init(|_| meta.advice_column());
        // for col in final_hash_bytes.into_iter() {
        //     meta.enable_equality(col);
        // }
        // State bits
        let mut w_ext = vec![0u64.expr(); NUM_BITS_PER_WORD_W];
        let mut w_2 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut w_7 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut w_15 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut w_16 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut a = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut b = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut c = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut d = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut e = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut f = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut g = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut h = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut d_64 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut h_64 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut new_a_ext = vec![0u64.expr(); NUM_BITS_PER_WORD_EXT];
        let mut new_e_ext = vec![0u64.expr(); NUM_BITS_PER_WORD_EXT];
        meta.create_gate("Query state bits", |meta| {
            for k in 0..NUM_BITS_PER_WORD_W {
                w_ext[k] = meta.query_advice(word_w[k], Rotation(-0));
            }
            for i in 0..NUM_BITS_PER_WORD {
                let k = i + NUM_BITS_PER_WORD_W - NUM_BITS_PER_WORD;
                w_2[i] = meta.query_advice(word_w[k], Rotation(-2));
                w_7[i] = meta.query_advice(word_w[k], Rotation(-7));
                w_15[i] = meta.query_advice(word_w[k], Rotation(-15));
                w_16[i] = meta.query_advice(word_w[k], Rotation(-16));
                let k = i + NUM_BITS_PER_WORD_EXT - NUM_BITS_PER_WORD;
                a[i] = meta.query_advice(word_a[k], Rotation(-1));
                b[i] = meta.query_advice(word_a[k], Rotation(-2));
                c[i] = meta.query_advice(word_a[k], Rotation(-3));
                d[i] = meta.query_advice(word_a[k], Rotation(-4));
                e[i] = meta.query_advice(word_e[k], Rotation(-1));
                f[i] = meta.query_advice(word_e[k], Rotation(-2));
                g[i] = meta.query_advice(word_e[k], Rotation(-3));
                h[i] = meta.query_advice(word_e[k], Rotation(-4));
                d_64[i] = meta.query_advice(word_a[k], Rotation(-((NUM_ROUNDS + 4) as i32)));
                h_64[i] = meta.query_advice(word_e[k], Rotation(-((NUM_ROUNDS + 4) as i32)));
            }
            for k in 0..NUM_BITS_PER_WORD_EXT {
                new_a_ext[k] = meta.query_advice(word_a[k], Rotation(0));
                new_e_ext[k] = meta.query_advice(word_e[k], Rotation(0));
            }
            vec![0u64.expr()]
        });
        let w = &w_ext[NUM_BITS_PER_WORD_W - NUM_BITS_PER_WORD..NUM_BITS_PER_WORD_W];
        let new_a = &new_a_ext[NUM_BITS_PER_WORD_EXT - NUM_BITS_PER_WORD..NUM_BITS_PER_WORD_EXT];
        let new_e = &new_e_ext[NUM_BITS_PER_WORD_EXT - NUM_BITS_PER_WORD..NUM_BITS_PER_WORD_EXT];

        let xor = |a: &[Expression<F>], b: &[Expression<F>]| {
            debug_assert_eq!(a.len(), b.len(), "invalid length");
            let mut c = vec![0.expr(); a.len()];
            for (idx, (a, b)) in a.iter().zip(b.iter()).enumerate() {
                c[idx] = xor::expr(a, b);
            }
            c
        };

        let select =
            |c: &[Expression<F>], when_true: &[Expression<F>], when_false: &[Expression<F>]| {
                debug_assert_eq!(c.len(), when_true.len(), "invalid length");
                debug_assert_eq!(c.len(), when_false.len(), "invalid length");
                let mut r = vec![0.expr(); c.len()];
                for (idx, (c, (when_true, when_false))) in c
                    .iter()
                    .zip(when_true.iter().zip(when_false.iter()))
                    .enumerate()
                {
                    r[idx] = select::expr(c.clone(), when_true.clone(), when_false.clone());
                }
                r
            };

        meta.create_gate("input checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            for w in w_ext.iter() {
                cb.require_boolean("w bit boolean", w.clone());
            }
            for a in new_a_ext.iter() {
                cb.require_boolean("a bit boolean", a.clone());
            }
            for e in new_e_ext.iter() {
                cb.require_boolean("e bit boolean", e.clone());
            }
            cb.gate(meta.query_fixed(q_enable, Rotation::cur()))
        });

        meta.create_gate("w extend", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let s0 = xor(
                &rotate::expr(&w_15, 7),
                &xor(&rotate::expr(&w_15, 18), &shift::expr(&w_15, 3)),
            );
            let s1 = xor(
                &rotate::expr(&w_2, 17),
                &xor(&rotate::expr(&w_2, 19), &shift::expr(&w_2, 10)),
            );
            let new_w =
                decode::expr(&w_16) + decode::expr(&s0) + decode::expr(&w_7) + decode::expr(&s1);
            cb.require_equal("w", new_w, decode::expr(&w_ext));
            cb.gate(meta.query_fixed(q_extend, Rotation::cur()))
        });

        meta.create_gate("compression", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let s1 = xor(
                &rotate::expr(&e, 6),
                &xor(&rotate::expr(&e, 11), &rotate::expr(&e, 25)),
            );
            let ch = select(&e, &f, &g);
            let temp1 = decode::expr(&h)
                + decode::expr(&s1)
                + decode::expr(&ch)
                + meta.query_fixed(round_cst, Rotation::cur())
                + decode::expr(w);

            let s0 = xor(
                &rotate::expr(&a, 2),
                &xor(&rotate::expr(&a, 13), &rotate::expr(&a, 22)),
            );
            let maj = select(&xor(&b, &c), &a, &b);
            let temp2 = decode::expr(&s0) + decode::expr(&maj);
            cb.require_equal(
                "compress a",
                decode::expr(&new_a_ext),
                temp1.clone() + temp2,
            );
            cb.require_equal(
                "compress e",
                decode::expr(&new_e_ext),
                decode::expr(&d) + temp1,
            );
            cb.gate(meta.query_fixed(q_compression, Rotation::cur()))
        });

        meta.create_gate("start", |meta| {
            let is_final = meta.query_advice(is_final, Rotation::cur());
            let h_a = meta.query_fixed(h_a, Rotation::cur());
            let h_e = meta.query_fixed(h_e, Rotation::cur());
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let new_a_ext = decode::expr(&new_a_ext);
            let new_e_ext = decode::expr(&new_e_ext);
            let new_ext = new_a_ext.clone() + (1u64 << 32).expr() * new_e_ext.clone();
            cb.require_equal(
                "start a",
                new_a_ext,
                select::expr(is_final.expr(), h_a, decode::expr(&d)),
            );
            cb.require_equal(
                "start e",
                new_e_ext,
                select::expr(is_final.expr(), h_e, decode::expr(&h)),
            );
            cb.require_equal(
                "input words",
                meta.query_advice(input_words, Rotation::cur()),
                new_ext,
            );
            cb.gate(meta.query_fixed(q_start, Rotation::cur()))
        });

        meta.create_gate("end", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            cb.require_equal(
                "end a",
                decode::expr(&new_a_ext),
                decode::expr(&d) + decode::expr(&d_64),
            );
            cb.require_equal(
                "end e",
                decode::expr(&new_e_ext),
                decode::expr(&h) + decode::expr(&h_64),
            );
            cb.gate(meta.query_fixed(q_end, Rotation::cur()))
        });

        // Enforce logic for when this block is the last block for a hash
        meta.create_gate("is final", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let is_padding = meta.query_advice(
                *is_paddings.last().unwrap(),
                Rotation(-((NUM_END_ROWS + NUM_ROUNDS - NUM_WORDS_TO_ABSORB) as i32) - 2),
            );
            let is_final_prev = meta.query_advice(is_final, Rotation::prev());
            let is_final = meta.query_advice(is_final, Rotation::cur()); // On the first row is_final needs to be enabled
            cb.condition(meta.query_fixed(q_first, Rotation::cur()), |cb| {
                cb.require_equal(
                    "is_final needs to remain the same",
                    is_final.expr(),
                    1.expr(),
                );
            }); // Get the correct is_final state from the padding selector
            cb.condition(
                and::expr(&[
                    meta.query_fixed(q_squeeze, Rotation::cur()),
                    not::expr(meta.query_advice(is_dummy, Rotation::cur())),
                ]),
                |cb| {
                    cb.require_equal(
                        "is_final needs to match the padding
          selector",
                        is_final.expr(),
                        is_padding,
                    );
                },
            ); // Copy the is_final state to the q_start rows
            cb.condition(
                and::expr(&[
                    meta.query_fixed(q_start, Rotation::cur())
                        - meta.query_fixed(q_first, Rotation::cur()),
                    1.expr() - is_final_prev.expr(),
                ]),
                |cb| {
                    cb.require_equal(
                        "is_final needs to remain the same",
                        is_final.expr(),
                        is_final_prev,
                    );
                },
            );
            cb.gate(1.expr())
        });

        meta.create_gate("is enabled", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let q_squeeze = meta.query_fixed(q_squeeze, Rotation::cur());
            let is_final = meta.query_advice(is_final, Rotation::cur());
            let is_enabled = meta.query_advice(is_output_enabled, Rotation::cur());
            // Only set is_enabled to true when is_final is true and it's a squeeze row
            cb.require_equal(
                "is_enabled := q_squeeze && is_final",
                is_enabled.expr(),
                and::expr(&[q_squeeze.expr(), is_final.expr()]),
            );
            cb.gate(meta.query_fixed(q_enable, Rotation::cur()))
        });

        let start_new_hash = |meta: &mut VirtualCells<F>| {
            // A new hash is started when the previous hash is done or on the first row
            meta.query_advice(is_final, Rotation::cur())
        };

        // Create bytes from input bits
        let input_bytes = to_le_bytes::expr(w);

        // Padding
        meta.create_gate("padding", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let prev_is_padding = meta.query_advice(*is_paddings.last().unwrap(), Rotation::prev());
            let q_padding = meta.query_fixed(q_padding, Rotation::cur());
            let q_padding_last = meta.query_fixed(q_padding_last, Rotation::cur());
            let length = meta.query_advice(input_len, Rotation::cur());
            let is_final_padding_row =
                meta.query_advice(*is_paddings.last().unwrap(), Rotation(-2));
            // All padding selectors need to be boolean
            for is_padding in is_paddings.iter() {
                let is_padding = meta.query_advice(*is_padding, Rotation::cur());
                cb.condition(meta.query_fixed(q_enable, Rotation::cur()), |cb| {
                    cb.require_boolean("is_padding boolean", is_padding);
                });
            }
            // Now for each padding selector
            for idx in 0..is_paddings.len() {
                // Previous padding selector can be on the previous row
                let is_padding_prev = if idx == 0 {
                    prev_is_padding.expr()
                } else {
                    meta.query_advice(is_paddings[idx - 1], Rotation::cur())
                };
                let is_padding = meta.query_advice(is_paddings[idx], Rotation::cur());
                let is_first_padding = is_padding.clone() - is_padding_prev.clone(); // Check padding transition 0 -> 1 done only once
                cb.condition(q_padding.expr(), |cb| {
                    cb.require_boolean("padding step boolean", is_first_padding.clone());
                });
                // Padding start/intermediate byte, all padding rows except the last one
                cb.condition(
                    and::expr([
                        (q_padding.expr() - q_padding_last.expr()),
                        is_padding.expr(),
                    ]),
                    |cb| {
                        // Input bytes need to be zero, or 128 if this is the first padding byte
                        cb.require_equal(
                            "padding start/intermediate byte",
                            input_bytes[idx].clone(),
                            is_first_padding.expr() * 128.expr(),
                        );
                    },
                );
                // Padding start/intermediate byte, last padding row but not in the final block
                cb.condition(
                    and::expr([
                        q_padding_last.expr(),
                        is_padding.expr(),
                        not::expr(is_final_padding_row.expr()),
                    ]),
                    |cb| {
                        // Input bytes need to be zero, or 128 if this is the first padding byte
                        cb.require_equal(
                            "padding start/intermediate byte",
                            input_bytes[idx].clone(),
                            is_first_padding.expr() * 128.expr(),
                        );
                    },
                );
            }
            // The last row containing input/padding data in the final block needs to
            // contain the length in bits (Only input lengths up to 2**32 - 1
            // bits are supported, which is lower than the spec of 2**64 - 1 bits)
            cb.condition(
                and::expr([
                    q_padding_last.expr(),
                    is_final_padding_row.expr(),
                    not::expr(meta.query_advice(is_dummy, Rotation::cur())),
                ]),
                |cb| {
                    cb.require_equal("padding length", decode::expr(w), length.expr() * 8.expr());
                },
            );
            cb.gate(1.expr())
        });

        // Length
        meta.create_gate("length", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let q_padding = meta.query_fixed(q_padding, Rotation::cur());
            let start_new_hash = start_new_hash(meta);
            let length_prev = meta.query_advice(input_len, Rotation::prev());
            let length = meta.query_advice(input_len, Rotation::cur());
            //let data_rlc_prev = meta.query_advice(data_rlc, Rotation::prev());
            //let data_rlc = meta.query_advice(data_rlc, Rotation::cur());
            // Update the length/data_rlc on rows where we absorb data
            cb.condition(q_padding.expr(), |cb| {
                // Length increases by the number of bytes that aren't padding
                // In a new block we have to start from 0 if the previous block was the final
                // one
                cb.require_equal(
                    "update length",
                    length.clone(),
                    length_prev.clone() * not::expr(start_new_hash.expr())
                        + sum::expr(is_paddings.iter().map(|is_padding| {
                            not::expr(meta.query_advice(*is_padding, Rotation::cur()))
                        })),
                );

                // Use intermediate cells to keep the degree low
                // let mut new_data_rlc = data_rlc_prev.clone() *
                // not::expr(start_new_hash.expr());
                // cb.require_equal(
                //     "initial data rlc",
                //     meta.query_advice(data_rlcs[0], Rotation::cur()),
                //     new_data_rlc,
                // );
                // new_data_rlc = meta.query_advice(data_rlcs[0],
                // Rotation::cur()); for (idx, (byte,
                // is_padding)) in     input_bytes.iter().
                // zip(is_paddings.iter()).enumerate() {
                //     let r = meta.query_advice(randomness, Rotation::cur());
                //     new_data_rlc = select::expr(
                //         meta.query_advice(*is_padding, Rotation::cur()),
                //         new_data_rlc.clone(),
                //         new_data_rlc.clone() * r + byte.clone(),
                //     );
                //     if idx < data_rlcs.len() - 1 {
                //         let next_data_rlc = meta.query_advice(data_rlcs[idx +
                // 1], Rotation::cur());         cb.
                // require_equal(             "intermediate data
                // rlc",             next_data_rlc.clone(),
                //             new_data_rlc,
                //         );
                //         new_data_rlc = next_data_rlc;
                //     }
                // }
                // cb.require_equal("update data rlc", data_rlc.clone(),
                // new_data_rlc);
            });
            cb.gate(1.expr())
        });

        // Make sure data is consistent between blocks
        meta.create_gate("cross block data consistency", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let start_new_hash = start_new_hash(meta);
            let to_const =
                |value: &String| -> &'static str { Box::leak(value.clone().into_boxed_str()) };
            let mut add = |name: &'static str, column: Column<Advice>| {
                let last_rot =
                    Rotation(-((NUM_END_ROWS + NUM_ROUNDS - NUM_WORDS_TO_ABSORB) as i32));
                let value_to_copy = meta.query_advice(column, last_rot);
                let prev_value = meta.query_advice(column, Rotation::prev());
                let cur_value = meta.query_advice(column, Rotation::cur()); // On squeeze rows fetch the last used value
                cb.condition(meta.query_fixed(q_squeeze, Rotation::cur()), |cb| {
                    cb.require_equal(
                        to_const(&format!("{} copy check", name)),
                        cur_value.expr(),
                        value_to_copy.expr(),
                    );
                });
                // On first rows keep the length the same, or reset the length when starting a
                // new hash
                cb.condition(
                    meta.query_fixed(q_start, Rotation::cur())
                        - meta.query_fixed(q_first, Rotation::cur()),
                    |cb| {
                        cb.require_equal(
                            to_const(&format!("{} equality check", name)),
                            cur_value.expr(),
                            prev_value.expr() * not::expr(start_new_hash.expr()),
                        );
                    },
                );
                // Set the value to zero on the first row
                cb.condition(meta.query_fixed(q_first, Rotation::cur()), |cb| {
                    cb.require_equal(
                        to_const(&format!("{} initialized to 0", name)),
                        cur_value.clone(),
                        0.expr(),
                    );
                });
            };
            add("length", input_len);
            // add("data_rlc", data_rlc);
            add("last padding", *is_paddings.last().unwrap());

            cb.gate(1.expr())
        });

        // Squeeze
        meta.create_gate("squeeze", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            // Squeeze out the hash
            let hash_parts = [new_a, &a, &b, &c, new_e, &e, &f, &g];
            let hash_bytes = hash_parts
                .iter()
                .flat_map(|part| to_le_bytes::expr(part))
                .collect::<Vec<_>>();
            println!("hash_bytes len {}", hash_bytes.len());
            let hash_words = hash_bytes
                .chunks(8)
                .map(|vals| {
                    let mut sum = 0u64.expr();
                    for idx in (0..8) {
                        sum = sum + vals[idx].clone() * (256u64 << idx).expr();
                    }
                    sum
                })
                .collect::<Vec<Expression<F>>>();
            println!("hash words len {}", hash_words.len());
            // let r = meta.query_advice(randomness, Rotation::cur());
            // let rlc = compose_rlc::expr(&hash_bytes, r);
            let output_words = (0..4)
                .map(|idx| meta.query_advice(output_words, Rotation(-(3 - idx))))
                .collect::<Vec<Expression<F>>>();
            for (hash_word, output_word) in hash_words.into_iter().zip(output_words) {
                cb.condition(start_new_hash(meta), |cb| {
                    cb.require_equal("output words check", hash_word, output_word);
                });
            }
            cb.gate(meta.query_fixed(q_squeeze, Rotation::cur()))
        });

        meta.create_gate("is_dummy check", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let is_dummy_change = meta.query_advice(is_dummy, Rotation::cur())
                - meta.query_advice(is_dummy, Rotation::prev());
            let is_final_prev = meta.query_advice(is_final, Rotation::prev());
            cb.require_boolean("is_dummy_change should be boolean", is_dummy_change.expr());
            cb.condition(is_dummy_change.expr(), |cb| {
                cb.require_equal("is_final_prev==1", is_final_prev, 1.expr());
            });
            cb.gate(and::expr(&[
                not::expr(meta.query_fixed(q_first, Rotation::cur())),
                meta.query_fixed(q_enable, Rotation::cur()),
            ]))
        });

        info!("degree: {}", meta.degree());

        Sha256BitConfig {
            q_enable,
            q_first,
            q_extend,
            q_start,
            q_compression,
            q_end,
            q_padding,
            q_padding_last,
            q_squeeze,
            word_w,
            word_a,
            word_e,
            is_final,
            is_paddings,
            is_dummy,
            round_cst,
            h_a,
            h_e,
            input_len,
            input_words,
            is_output_enabled,
            output_words,
            _marker: PhantomData,
        }
    }

    fn assign(
        &self,
        region: &mut Region<'_, F>,
        witness: &[ShaRow<F>],
    ) -> Result<Vec<Sha256AssignedRow<F>>, Error> {
        let size = witness.len();
        let mut assigned_rows = Vec::new();
        for (offset, sha256_row) in witness.iter().enumerate() {
            assigned_rows.push(self.set_row(region, offset, sha256_row)?);
        }
        Ok(assigned_rows)
        // let first_r = region.assign_advice(
        //     || format!("randomness {}", 0),
        //     self.randomness,
        //     0,
        //     || Value::known(r),
        // )?;
        // for offset in 1..size {
        //     region.assign_advice(
        //         || format!("randomness {}", offset),
        //         self.randomness,
        //         offset,
        //         || Value::known(r),
        //     )?;
        // }
    }

    fn set_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        row: &ShaRow<F>,
    ) -> Result<Sha256AssignedRow<F>, Error> {
        let round = offset % (NUM_ROUNDS + 8);
        // Fixed values
        for (name, column, value) in &[
            ("q_enable", self.q_enable, F::from(true)),
            ("q_first", self.q_first, F::from(offset == 0)),
            (
                "q_extend",
                self.q_extend,
                F::from((4 + 16..4 + NUM_ROUNDS).contains(&round)),
            ),
            (
                "q_compression",
                self.q_compression,
                F::from((4..NUM_ROUNDS + 4).contains(&round)),
            ),
            ("q_end", self.q_end, F::from(round >= NUM_ROUNDS + 4)),
            (
                "q_padding",
                self.q_padding,
                F::from((4..20).contains(&round)),
            ),
            ("q_padding_last", self.q_padding_last, F::from(round == 19)),
            (
                "q_squeeze",
                self.q_squeeze,
                F::from(round == NUM_ROUNDS + 7),
            ),
            (
                "round_cst",
                self.round_cst,
                F::from(if (4..NUM_ROUNDS + 4).contains(&round) {
                    ROUND_CST[round - 4] as u64
                } else {
                    0
                }),
            ),
            (
                "Ha",
                self.h_a,
                F::from(if round < 4 { H[3 - round] as u64 } else { 0 }),
            ),
            (
                "He",
                self.h_e,
                F::from(if round < 4 { H[7 - round] as u64 } else { 0 }),
            ),
        ] {
            region.assign_fixed(
                || format!("assign {} {}", name, offset),
                *column,
                offset,
                || Value::known(*value),
            )?;
        }

        let q_start = region.assign_fixed(
            || format!("assign {} {}", "q_start", offset),
            self.q_start,
            offset,
            || Value::known(F::from(round < 4)),
        )?;

        // Advice values
        for (name, columns, values) in [
            ("w bits", self.word_w.as_slice(), row.w.as_slice()),
            ("a bits", self.word_a.as_slice(), row.a.as_slice()),
            ("e bits", self.word_e.as_slice(), row.e.as_slice()),
            (
                "padding selectors",
                self.is_paddings.as_slice(),
                row.is_paddings.as_slice(),
            ),
            (
                "is_final",
                [self.is_final].as_slice(),
                [row.is_final].as_slice(),
            ),
            (
                "is_dummy",
                [self.is_dummy].as_slice(),
                [row.is_dummy].as_slice(),
            ),
        ] {
            for (idx, (value, column)) in values.iter().zip(columns.iter()).enumerate() {
                region.assign_advice(
                    || format!("assign {} {} {}", name, idx, offset),
                    *column,
                    offset,
                    || Value::known(F::from(*value)),
                )?;
            }
        }

        let is_output_enabled = region.assign_advice(
            || format!("assign {} {} {}", "is_output_enabled", 0, offset),
            self.is_output_enabled,
            offset,
            || Value::known(F::from(row.is_final && round == NUM_ROUNDS + 7)),
        )?;

        let input_len = region.assign_advice(
            || format!("assign {} {} {}", "length", 0, offset),
            self.input_len,
            offset,
            || Value::known(F::from(row.length as u64)),
        )?;

        let input_word = region.assign_advice(
            || format!("assign {} {} {}", "input_word", 0, offset),
            self.input_words,
            offset,
            || Value::known(row.input_word),
        )?;

        let output_word = region.assign_advice(
            || format!("assign {} {} {}", "output_word", 0, offset),
            self.output_words,
            offset,
            || Value::known(row.output_word),
        )?;

        // Data rlcs
        // for (idx, (data_rlc, column)) in
        // row.data_rlcs.iter().zip(self.data_rlcs.iter()).enumerate() {
        //     region.assign_advice(
        //         || format!("assign data rlcs {} {}", idx, offset),
        //         *column,
        //         offset,
        //         || Value::known(*data_rlc),
        //     )?;
        // }

        // Hash data
        // self.hash_table.assign_row(
        //     region,
        //     offset,
        //     [
        //         F::from(row.is_final && round == NUM_ROUNDS + 7),
        //         row.data_rlc,
        //         F::from(row.length as u64),
        //         row.hash_rlc,
        //     ],
        // )?;

        /*let mut hash_cells = Vec::with_capacity(NUM_BYTES_FINAL_HASH);
        if !row.is_final || round != NUM_ROUNDS + 7 {
            for idx in 0..(NUM_BYTES_FINAL_HASH) {
                region.assign_advice(
                    || format!("final hash word at {}", idx),
                    self.final_hash_bytes[idx],
                    offset,
                    || Value::known(F::from(0u64)),
                )?;
                //hash_cells.push(cell);
            }
        } else {
            for (idx, byte) in row.final_hash_bytes.iter().enumerate() {
                let cell = region.assign_advice(
                    || format!("final hash word at {}", idx),
                    self.final_hash_bytes[idx],
                    offset,
                    || Value::known(*byte),
                )?;
                hash_cells.push(cell);
            }
        }*/
        Ok(Sha256AssignedRow {
            offset,
            q_start,
            input_len,
            input_word,
            is_output_enabled,
            output_word,
        })
    }
}

fn sha256<F: Field>(bytes: &[u8], max_input_len: usize) -> Vec<ShaRow<F>> {
    let mut bits = into_bits(bytes);
    let mut rows = Vec::<ShaRow<F>>::new();
    // Padding
    let length = bits.len();
    let mut length_in_bits = into_bits(&(length as u64).to_be_bytes());
    assert!(length_in_bits.len() == NUM_BITS_PADDING_LENGTH);
    bits.push(1);
    while (bits.len() + NUM_BITS_PADDING_LENGTH) % RATE_IN_BITS != 0 {
        bits.push(0);
    }
    bits.append(&mut length_in_bits);
    assert!(bits.len() % RATE_IN_BITS == 0);
    let target_round = bits.len() / RATE_IN_BITS - 1;
    let mut dummy_inputs = vec![0u8; 8 * max_input_len - bits.len()];
    bits.append(&mut dummy_inputs);

    // Set the initial state
    let mut hs: [u64; 8] = H
        .iter()
        .map(|v| *v as u64)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let mut length = 0usize;
    let mut data_rlc = F::zero();
    let mut in_padding = false;

    // Process each block
    let chunks = bits.chunks(RATE_IN_BITS);
    for (idx, chunk) in chunks.enumerate() {
        // Adds a row
        let mut add_row = |w: u64,
                           a: u64,
                           e: u64,
                           is_final,
                           is_dummy,
                           length,
                           is_paddings,
                           input_word,
                           output_word| {
            let word_to_bits = |value: u64, num_bits: usize| {
                into_bits(&value.to_be_bytes())[64 - num_bits..64]
                    .iter()
                    .map(|b| *b != 0)
                    .into_iter()
                    .collect::<Vec<_>>()
            };
            rows.push(ShaRow {
                w: word_to_bits(w, NUM_BITS_PER_WORD_W).try_into().unwrap(),
                a: word_to_bits(a, NUM_BITS_PER_WORD_EXT).try_into().unwrap(),
                e: word_to_bits(e, NUM_BITS_PER_WORD_EXT).try_into().unwrap(),
                is_final,
                is_dummy,
                length,
                is_paddings,
                input_word,
                output_word,
            });
        };

        // Last block for this hash
        let is_final_block = idx == target_round; //num_chunks - 1;

        // Set the state
        let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h) =
            (hs[0], hs[1], hs[2], hs[3], hs[4], hs[5], hs[6], hs[7]);

        // Add start rows
        let mut add_row_start = |a: u64, e: u64, is_final| {
            add_row(
                0,
                a,
                e,
                is_final,
                idx > target_round,
                length,
                [false, false, false, in_padding],
                F::from(a) + F::from(e << 32),
                F::zero(),
            )
        };
        add_row_start(d, h, idx == 0);
        add_row_start(c, g, idx == 0);
        add_row_start(b, f, idx == 0);
        add_row_start(a, e, idx == 0);

        let mut ws = Vec::new();
        for (round, round_cst) in ROUND_CST.iter().enumerate() {
            // Padding/Length/Data rlc
            let mut is_paddings = [false; ABSORB_WIDTH_PER_ROW_BYTES];
            //let mut data_rlcs = [F::zero(); ABSORB_WIDTH_PER_ROW_BYTES];
            if round < NUM_WORDS_TO_ABSORB {
                // padding/length
                for is_padding in is_paddings.iter_mut() {
                    *is_padding = if length == bytes.len() {
                        true
                    } else {
                        length += 1;
                        false
                    };
                }
                // data rlc
                let input_bytes = to_le_bytes::value(&chunk[round * 32..(round + 1) * 32]);
                //data_rlcs[0] = data_rlc;
                // for (idx, (byte, padding)) in
                // input_bytes.iter().zip(is_paddings.iter()).enumerate() {
                //     if !*padding {
                //         data_rlc = data_rlc * r + F::from(*byte as u64);
                //     }
                //     if idx < data_rlcs.len() - 1 {
                //         data_rlcs[idx + 1] = data_rlc;
                //     }
                // }
                in_padding = *is_paddings.last().unwrap();
            }

            // w
            let w_ext = if round < NUM_WORDS_TO_ABSORB {
                decode::value(&chunk[round * 32..(round + 1) * 32])
            } else {
                let get_w = |offset: usize| ws[ws.len() - offset] & 0xFFFFFFFF;
                let s0 = rotate::value(get_w(15), 7)
                    ^ rotate::value(get_w(15), 18)
                    ^ shift::value(get_w(15), 3);
                let s1 = rotate::value(get_w(2), 17)
                    ^ rotate::value(get_w(2), 19)
                    ^ shift::value(get_w(2), 10);
                get_w(16) + s0 + get_w(7) + s1
            };
            let w = w_ext & 0xFFFFFFFF;
            ws.push(w);

            // compression
            let s1 = rotate::value(e, 6) ^ rotate::value(e, 11) ^ rotate::value(e, 25);
            let ch = (e & f) ^ (!e & g);
            let temp1 = h + s1 + ch + (*round_cst as u64) + w;
            let s0 = rotate::value(a, 2) ^ rotate::value(a, 13) ^ rotate::value(a, 22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0 + maj;

            h = g;
            g = f;
            f = e;
            e = d + temp1;
            d = c;
            c = b;
            b = a;
            a = temp1 + temp2;

            // Add the row
            add_row(
                w_ext,
                a,
                e,
                false,
                idx > target_round,
                if round < NUM_WORDS_TO_ABSORB {
                    length
                } else {
                    0
                },
                is_paddings,
                F::zero(),
                F::zero(),
            );

            // Truncate the newly calculated values
            a &= 0xFFFFFFFF;
            e &= 0xFFFFFFFF;
        }

        // Accumulate
        hs[0] += a;
        hs[1] += b;
        hs[2] += c;
        hs[3] += d;
        hs[4] += e;
        hs[5] += f;
        hs[6] += g;
        hs[7] += h;

        // if (idx == target_round) {
        //     let hash_bytes = hs
        //         .iter()
        //         .flat_map(|h| (*h as u32).to_be_bytes())
        //         .collect::<Vec<_>>();
        //     debug!("hash: {:x?}", &hash_bytes);
        //     debug!("data rlc: {:x?}", data_rlc);
        // }

        // Squeeze

        // let hash_rlc = if is_final_block {
        //     let hash_bytes = hs
        //         .iter()
        //         .flat_map(|h| (*h as u32).to_be_bytes())
        //         .collect::<Vec<_>>();
        //     rlc::value(&hash_bytes, r)
        // } else {
        //     F::zero()
        // };

        let hash_words = if is_final_block {
            let hash_bytes = hs
                .iter()
                .flat_map(|h| (*h as u32).to_be_bytes())
                .collect::<Vec<_>>();
            hash_bytes
                .chunks(8)
                .map(|vals| {
                    let mut sum = 0u64;
                    for idx in (0..8) {
                        sum = sum + (vals[idx] as u64) * (256u64 << idx);
                        println!("idx {} byte {:?} sum {:?}", idx, vals[idx], sum);
                    }
                    sum
                })
                .collect()
        } else {
            vec![0u64; 4]
        };

        // Add end rows
        let mut add_row_end = |a: u64, e: u64, output_word: F| {
            add_row(
                0,
                a,
                e,
                false,
                idx > target_round,
                0,
                [false; ABSORB_WIDTH_PER_ROW_BYTES],
                F::zero(),
                output_word,
            )
        };
        add_row_end(hs[3], hs[7], F::from(hash_words[0]));
        add_row_end(hs[2], hs[6], F::from(hash_words[1]));
        add_row_end(hs[1], hs[5], F::from(hash_words[2]));
        add_row(
            0,
            hs[0],
            hs[4],
            is_final_block,
            idx > target_round,
            length,
            [false, false, false, in_padding],
            F::zero(),
            F::from(hash_words[3]),
        );

        // Now truncate the results
        for h in hs.iter_mut() {
            *h &= 0xFFFFFFFF;
        }
    }
    rows
}

// fn multi_sha256<F: Field>(bytes: &[Vec<u8>], r: F) -> Vec<ShaRow<F>> {
//     let mut rows: Vec<ShaRow<F>> = Vec::new();
//     for bytes in bytes {
//         sha256(&mut rows, bytes, r);
//     }
//     rows
// }

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

    #[derive(Debug, Clone)]
    struct TestSha256Config<F: Field> {
        sha256_config: Sha256BitConfig<F>,
        instance: Column<Instance>,
    }

    #[derive(Default, Debug, Clone)]
    struct TestSha256<F: Field> {
        input: Vec<u8>,
        max_input_len: usize,
        _f: PhantomData<F>,
    }

    impl<F: Field> Circuit<F> for TestSha256<F> {
        type Config = TestSha256Config<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unimplemented!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let sha256_config = Sha256BitConfig::configure(meta);
            let instance = meta.instance_column();
            meta.enable_equality(instance);
            Self::Config {
                sha256_config,
                instance,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let sha256chip = Sha256BitChip::new(config.sha256_config.clone(), self.max_input_len);
            layouter.assign_region(
                || "digest",
                |mut region| sha256chip.digest(&mut region, &self.input),
            )?;
            //layouter.constrain_instance(first_r.cell(), config.instance, 0)?;
            Ok(())
        }
    }

    use rand::{thread_rng, Rng};
    fn verify<F: Field>(k: u32, input: Vec<u8>, max_input_len: usize, success: bool) {
        let rng = thread_rng();
        let circuit = TestSha256 {
            input,
            max_input_len,
            _f: PhantomData,
        };

        let prover = MockProver::<F>::run(k, &circuit, vec![vec![]]).unwrap();
        let verify_result = prover.verify();
        if verify_result.is_ok() != success {
            if let Some(errors) = verify_result.err() {
                for error in errors.iter() {
                    println!("{}", error);
                }
            }
            panic!();
        }
    }

    #[test]
    fn bit_sha256_simple1() {
        let k = 8;
        let inputs = (0u8..55).collect::<Vec<_>>();
        verify::<Fr>(k, inputs, 128, true);
    }

    #[test]
    fn bit_sha256_simple2() {
        let k = 11;
        let inputs = vec![1u8; 1000];
        verify::<Fr>(k, inputs, 1024, true);
    }
}
