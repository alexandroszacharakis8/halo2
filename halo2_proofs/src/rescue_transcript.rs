//! This module contains utilities and traits for dealing with Fiat-Shamir
//! transcripts.

use group::ff::{FromUniformBytes, PrimeField, Field};
use midnight_circuits::{RescueParametersPallas, RescueSponge};

use crate::arithmetic::{Coordinates, CurveAffine};

use std::io::{self, Read, Write};
use group::GroupEncoding;
use pasta_curves::{EqAffine, Fp, Fq};
use crate::transcript::{EncodedChallenge, Transcript, TranscriptRead, TranscriptWrite};

/// RescueRead used for a rescue-based transcript
#[derive(Debug, Clone)]
pub struct RescueRead<R: Read> {
    state: Vec<Fp>,
    reader: R,
}

impl<R: Read> RescueRead<R> {
    /// Initialize a transcript given an input buffer.
    pub fn init(reader: R) -> Self {
        let mut u_repr = <Fp as PrimeField>::Repr::default();
        u_repr[..16].as_mut().copy_from_slice(b"Halo2-Transcript");
        RescueRead {
            state: vec![Fp::from_repr(u_repr).expect("blackbird")],
            reader,
        }
    }
}

impl<R: Read> TranscriptRead<EqAffine, Fp>
for RescueRead<R>
{
    fn read_point(&mut self) -> io::Result<EqAffine> {
        let mut compressed = <EqAffine as GroupEncoding>::Repr::default();
        self.reader.read_exact(compressed.as_mut())?;
        let point: EqAffine = Option::from(EqAffine::from_bytes(&compressed)).ok_or_else(|| {
            io::Error::new(io::ErrorKind::Other, "invalid point encoding in proof")
        })?;
        self.common_point(point)?;

        Ok(point)
    }

    fn read_scalar(&mut self) -> io::Result<Fp> {
        let mut data = <Fp as PrimeField>::Repr::default();
        self.reader.read_exact(data.as_mut())?;
        let scalar: Fp = Option::from(Fp::from_repr(data)).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Other,
                "invalid field element encoding in proof",
            )
        })?;
        self.common_scalar(scalar)?;

        Ok(scalar)
    }
}

impl<R: Read> Transcript<EqAffine, Fp> for RescueRead<R>
{
    fn squeeze_challenge(&mut self) -> Fp {
        self.state.extend_from_slice(&[Fp::ZERO]);
        let hasher = self.state.clone();
        let mut bytes = [0u8; 64];
        bytes[..32].copy_from_slice(&RescueSponge::<Fp, RescueParametersPallas>::hash(&hasher, Some(padding_fn)).to_repr());
        <Fp as EncodedChallenge<EqAffine>>::new(&bytes)
    }

    fn common_point(&mut self, point: EqAffine) -> io::Result<()> {
        self.state.extend_from_slice(&[Fp::ONE]);
        let coords: Coordinates<EqAffine> = Option::from(point.coordinates()).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Other,
                "cannot write points at infinity to the transcript",
            )
        })?;
        self.state.push(base_as_scalar(coords.x()));
        self.state.push(base_as_scalar(coords.y()));

        Ok(())
    }

    fn common_scalar(&mut self, scalar: Fp) -> io::Result<()> {
        self.state.push(Fp::from(2));
        self.state.push(scalar);

        Ok(())
    }
}

/// RescueWrite, used for a rescue-based transcript
#[derive(Debug, Clone)]
pub struct RescueWrite<W: Write> {
    state: Vec<Fp>,
    writer: W,
}

impl<W: Write> RescueWrite<W> {
    /// Initialize a transcript given an output buffer.
    pub fn init(writer: W) -> Self {
        let mut scalar_bytes = [0u8; 32];
        scalar_bytes[..16].copy_from_slice(b"Halo2-Transcript");
        RescueWrite {
            state: vec![Fp::from_repr(scalar_bytes).expect("Meh")],
            writer,
        }
    }

    /// Conclude the interaction and return the output buffer (writer).
    pub fn finalize(self) -> W {
        // TODO: handle outstanding scalars? see issue #138
        self.writer
    }
}

impl<W: Write> TranscriptWrite<EqAffine, Fp>
for RescueWrite<W>
{
    fn write_point(&mut self, point: EqAffine) -> io::Result<()> {
        self.common_point(point)?;
        let compressed = point.to_bytes();
        self.writer.write_all(compressed.as_ref())
    }
    fn write_scalar(&mut self, scalar: Fp) -> io::Result<()> {
        self.common_scalar(scalar)?;
        let data = scalar.to_repr();
        self.writer.write_all(data.as_ref())
    }
}

impl<W: Write> Transcript<EqAffine, Fp>
for RescueWrite<W>
{
    fn squeeze_challenge(&mut self) -> Fp {
        self.state.push(Fp::ZERO);
        let hasher = self.state.clone();
        RescueSponge::<Fp, RescueParametersPallas>::hash(&hasher, Some(padding_fn))
    }

    fn common_point(&mut self, point: EqAffine) -> io::Result<()> {
        self.state.push(Fp::ONE);
        let coords: Coordinates<EqAffine> = Option::from(point.coordinates()).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Other,
                "cannot write points at infinity to the transcript",
            )
        })?;
        self.state.push(base_as_scalar(coords.x()));
        self.state.push(base_as_scalar(coords.y()));

        Ok(())
    }

    fn common_scalar(&mut self, scalar: Fp) -> io::Result<()> {
        self.state.push(Fp::from(2));
        self.state.push(scalar);

        Ok(())
    }
}

impl EncodedChallenge<EqAffine> for Fp
{
    type Input = [u8; 64];

    fn new(challenge_input: &[u8; 64]) -> Self {
        Fp::from_uniform_bytes(challenge_input)
    }
    fn get_scalar(&self) -> Fp {
        *self
    }
}

fn padding_fn(input: &[Fp]) -> Vec<Fp> {
    let mut out = vec![Fp::ZERO; (((input.len() - 1) / 3) + 1) * 3];
    out[..input.len()].copy_from_slice(input);
    out
}

fn base_as_scalar(base: &Fq) -> Fp {
    let mut bytes_wide = [0u8; 64];
    bytes_wide[..32].copy_from_slice(base.to_repr().as_ref());

    Fp::from_uniform_bytes(&bytes_wide)
}
