//! This module contains utilities and traits for dealing with Fiat-Shamir
//! transcripts.

use group::ff::{Field, FromUniformBytes, PrimeField};
use midnight_circuits::parameters::RescueParametersPallas;
use midnight_circuits::primitives::crhf::RescueSponge;

use crate::arithmetic::CurveAffine;

use crate::transcript::{EncodedChallenge, Transcript, TranscriptRead, TranscriptWrite};
use group::GroupEncoding;
use pasta_curves::{EqAffine, Fp, Fq};
use std::io::{self, Read, Write};

/// RescueRead used for a rescue-based transcript
#[derive(Debug, Clone)]
pub struct RescueRead<R: Read> {
    // the state is a rescue sponge
    state: RescueSponge<Fp, RescueParametersPallas>,
    reader: R,
}

impl<R: Read> RescueRead<R> {
    /// Initialize a transcript given an input buffer.
    pub fn init(reader: R) -> Self {
        // initialize state with (0,0,0,0)
        let mut state = RescueSponge::new();

        // we update the state by hashing "Halo2-Transcript"
        let mut u_repr = <Fp as PrimeField>::Repr::default();
        u_repr[..16].as_mut().copy_from_slice(b"Halo2-Transcript");
        let msg = Fp::from_repr(u_repr).expect("blackbird");

        // apply the hash to update the sponge
        state.absorb([msg, Fp::ZERO, Fp::ZERO]);
        RescueRead {
            // initial state is Hash(Halo2-Transcript, 0, 0, 0)
            state,
            reader,
        }
    }
}

impl<R: Read> TranscriptRead<EqAffine, Fp> for RescueRead<R> {
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

impl<R: Read> Transcript<EqAffine, Fp> for RescueRead<R> {
    fn squeeze_challenge(&mut self) -> Fp {
        // absorb (0,0,0) to state for domain separation
        self.state.absorb([Fp::ZERO, Fp::ZERO, Fp::ZERO]);
        // squeeze the sponge to get the challenge 
        self.state.squeeze()[0]
    }

    fn common_point(&mut self, point: EqAffine) -> io::Result<()> {
        // TODO: fix error handling
        let x = *point.coordinates().unwrap().x();
        let y = *point.coordinates().unwrap().y();

        // absorb (1, x, y) to the sponge
        self.state.absorb([Fp::from(1), base_as_scalar(&x), base_as_scalar(&y)]);

        Ok(())
    }

    fn common_scalar(&mut self, scalar: Fp) -> io::Result<()> {
        // absorb (2, 0, scalar) to the sponge
        self.state.absorb([Fp::from(2), Fp::ZERO, scalar]);

        Ok(())
    }
}

/// RescueWrite, used for a rescue-based transcript
#[derive(Debug, Clone)]
pub struct RescueWrite<W: Write> {
    state: RescueSponge<Fp, RescueParametersPallas>,
    writer: W,
}

impl<W: Write> RescueWrite<W> {
    /// Initialize a transcript given an output buffer.
    pub fn init(writer: W) -> Self {
        // initialize state with (0,0,0,0)
        let mut state = RescueSponge::new();

        // we update the state by hashing "Halo2-Transcript"
        let mut u_repr = <Fp as PrimeField>::Repr::default();
        u_repr[..16].as_mut().copy_from_slice(b"Halo2-Transcript");
        let msg = Fp::from_repr(u_repr).expect("blackbird");

        // apply the hash to update the sponge
        state.absorb([msg, Fp::ZERO, Fp::ZERO]);
        RescueWrite {
            // initial state is Hash(Halo2-Transcript, 0, 0, 0)
            state,
            writer,
        }
    }

    /// Conclude the interaction and return the output buffer (writer).
    pub fn finalize(self) -> W {
        // TODO: handle outstanding scalars? see issue #138
        self.writer
    }
}

impl<W: Write> TranscriptWrite<EqAffine, Fp> for RescueWrite<W> {
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

impl<W: Write> Transcript<EqAffine, Fp> for RescueWrite<W> {
    fn squeeze_challenge(&mut self) -> Fp {
        // absorb (0,0,0) to state for domain separation
        self.state.absorb([Fp::ZERO, Fp::ZERO, Fp::ZERO]);
        // squeeze the sponge to get the challenge 
        self.state.squeeze()[0]
    }

    fn common_point(&mut self, point: EqAffine) -> io::Result<()> {
        // TODO: fix error handling
        let x = *point.coordinates().unwrap().x();
        let y = *point.coordinates().unwrap().y();

        // absorb (1, x, y) to the sponge
        self.state.absorb([Fp::from(1), base_as_scalar(&x), base_as_scalar(&y)]);

        Ok(())
    }

    fn common_scalar(&mut self, scalar: Fp) -> io::Result<()> {
        // absorb (2, 0, scalar) to the sponge
        self.state.absorb([Fp::from(2), Fp::ZERO, scalar]);

        Ok(())
    }
}

impl EncodedChallenge<EqAffine> for Fp {
    type Input = [u8; 64];

    fn new(challenge_input: &[u8; 64]) -> Self {
        Fp::from_uniform_bytes(challenge_input)
    }
    fn get_scalar(&self) -> Fp {
        *self
    }
}

// FIXME: don't release anything using this
fn base_as_scalar(base: &Fq) -> Fp {
    let mut bytes_wide = [0u8; 64];
    bytes_wide[..32].copy_from_slice(base.to_repr().as_ref());

    Fp::from_uniform_bytes(&bytes_wide)
}
