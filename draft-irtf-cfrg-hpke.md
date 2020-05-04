---
title: Hybrid Public Key Encryption
abbrev: HPKE
docname: draft-irtf-cfrg-hpke-latest
date:
category: info

ipr: trust200902
keyword: Internet-Draft

stand_alone: yes
pi: [toc, sortrefs, symrefs]

author:
 -  ins: R. L. Barnes
    name: Richard L. Barnes
    org: Cisco
    email: rlb@ipv.sx
 -  ins: K. Bhargavan
    name: Karthik Bhargavan
    org: Inria
    email: karthikeyan.bhargavan@inria.fr
 -  ins: C. A. Wood
    name: Christopher A. Wood
    org: Cloudflare
    email: caw@heapingbits.net

informative:
  CS01:
    title: Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack
    target: https://eprint.iacr.org/2001/108
    date: 2001
    authors:
      -
        ins: Ronald Cramer
      -
        ins: Victor Shoup

  GAP:
    title: The Gap-Problems - a New Class of Problems for the Security of Cryptographic Schemes
    target: https://link.springer.com/content/pdf/10.1007/3-540-44586-2_8.pdf
    date: 2001
    authors:
      -
        ins: Tatsuaki Okamoto
      -
        ins: David Pointcheval
    seriesinfo:
      ISBN: 978-3-540-44586-9

  ANSI:
    title: Public Key Cryptography for the Financial Services Industry -- Key Agreement and Key Transport Using Elliptic Curve Cryptography
    date: 2001
    authors:
      -
        ins:
        org: American National Standards Institute

  IEEE:
    title: IEEE 1363a, Standard Specifications for Public Key Cryptography - Amendment 1 -- Additional Techniques
    date: 2004
    authors:
      -
        ins:
        org: Institute of Electrical and Electronics Engineers

  ISO:
    title: ISO/IEC 18033-2, Information Technology - Security Techniques - Encryption Algorithms - Part 2 -- Asymmetric Ciphers
    date: 2006
    authors:
      -
        ins:
        org: International Organization for Standardization / International Electrotechnical Commission

  SECG:
    title: Elliptic Curve Cryptography, Standards for Efficient Cryptography Group, ver. 2
    target: https://secg.org/sec1-v2.pdf
    date: 2009

  HPKEAnalysis:
    title: An Analysis of Hybrid Public Key Encryption
    target: https://eprint.iacr.org/2020/243.pdf
    date: 2020
    authors:
      -
        ins: Benjamin Lipp
        org: INRIA Paris

  MAEA10:
    title: A Comparison of the Standardized Versions of ECIES
    target: http://sceweb.sce.uhcl.edu/yang/teaching/csci5234WebSecurityFall2011/Chaum-blind-signatures.PDF
    date: 2010
    authors:
      -
        ins: V. Gayoso Martinez
        org: Applied Physics Institute, CSIC, Madrid, Spain
      -
        ins: F. Hernandez Alvarez
        org: Applied Physics Institute, CSIC, Madrid, Spain
      -
        ins: L. Hernandez Encinas
        org: Applied Physics Institute, CSIC, Madrid, Spain
      -
        ins: C. Sanchez Avila
        org: Polytechnic University, Madrid, Spain

  BNT19:
    title: "Nonces Are Noticed: AEAD Revisited"
    target: http://dx.doi.org/10.1007/978-3-030-26948-7_9
    date: 2019
    authors:
      -
        ins: M. Bellare
        org: University of California, San Diego
      -
        ins: R. Ng
        org: University of California, San Diego
      -
        ins: B. Tackmann
        org: IBM Research

  JKR96:
    title: Designated Verifier Proofs and Their Applications
    target: https://doi.org/10.1007%2F3-540-49677-7_30
    date: 1996
    authors:
      -
        ins: M. Jakobsson
        org: University of California, San Diego
      -
        ins: K. Sako
        org: NEC Corporation
      -
        ins: R. Impagliazzo
        org: University of California, San Diego

  TestVectors:
    title: HPKE Test Vectors
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/ab48bdc737655f1b64dce898596648d943d9ba61/test-vectors.json
    date: 2019

  keyagreement: DOI.10.6028/NIST.SP.800-56Ar3

  NISTCurves: DOI.10.6028/NIST.FIPS.186-4

  GCM: DOI.10.6028/NIST.SP.800-38D

  fiveG:
    title: Security architecture and procedures for 5G System
    target: https://portal.3gpp.org/desktopmodules/Specifications/SpecificationDetails.aspx?specificationId=3169
    date: 2019

  HMAC:
    title: To Hash or Not to Hash Again? (In)differentiability Results for H^2 and HMAC
    target: https://eprint.iacr.org/2013/382
    date: 2013
    authors:
      -
        ins: Y. Dodis
        org: Department of Computer Science, New York University
      -
        ins: Thomas Ristenpart
        org: Department of Computer Sciences, University of Wisconsin–Madison
      -
        ins: John Steinberger
        org: Institute of Theoretical Computer Science, Tsinghua University
      -
        ins: Stefano Tessaro
        org: CSAIL, Massachusetts Institute of Technology

--- abstract

This document describes a scheme for hybrid public-key encryption
(HPKE).  This scheme provides authenticated public key encryption of
arbitrary-sized plaintexts for a recipient public key. HPKE works
for any combination of an asymmetric key encapsulation mechanism
(KEM), key derivation function (KDF), and authenticated encryption
with additional data (AEAD) encryption function. We provide
instantiations of the scheme using widely-used and efficient
primitives.

--- middle

# Introduction

"Hybrid" public-key encryption schemes (HPKE) that combine
asymmetric and symmetric algorithms are a substantially more
efficient solution than traditional public key encryption techniques
such as those based on RSA or ElGamal.  Encrypted messages convey an encryption
key encapsulated with a public-key scheme, along with one or more ciphertexts
encrypted using that key.  This type of public key encryption has many
applications in practice, for example:

* PGP {{?RFC6637}}
* Messaging Layer Security {{?I-D.ietf-mls-protocol}}
* Encrypted Server Name Indication {{?I-D.ietf-tls-esni}}
* Protection of 5G subscriber identities {{fiveG}}

Currently, there are numerous competing and non-interoperable standards and
variants for hybrid encryption, mostly based on ECIES, including ANSI X9.63
(ECIES) {{ANSI}}, IEEE 1363a {{IEEE}}, ISO/IEC 18033-2 {{ISO}}, and SECG SEC 1
{{SECG}}.  See {{MAEA10}} for a thorough comparison.  All of these existing
schemes have problems, e.g., because they rely on outdated primitives, lack
proofs of IND-CCA2 security, or fail to provide test vectors.

This document defines an HPKE scheme that provides a subset
of the functions provided by the collection of schemes above, but
specified with sufficient clarity that they can be interoperably
implemented and formally verified. It is secure against (adaptive)
chosen ciphertext attacks (IND-CCA2 secure) under classical assumptions
about the underlying primitives {{HPKEAnalysis}}. A summary of this
analysis is in {{sec-properties}}.

# Requirements Notation

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT",
"SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and
"OPTIONAL" in this document are to be interpreted as described in
BCP14 {{!RFC2119}} {{!RFC8174}}  when, and only when, they appear in
all capitals, as shown here.

# Notation

The following terms are used throughout this document to describe the
operations, roles, and behaviors of HPKE:

- Sender (S): Entity which sends an encrypted message.
- Recipient (R): Entity which receives an encrypted message.
- Ephemeral (E): A fresh random value meant for one-time use.
- `(skX, pkX)`: A KEM key pair used in role X; `skX` is the private
  key and `pkX` is the public key
- `pk(skX)`: The public key corresponding to private key `skX`
- `encode_big_endian(x, n)`: An byte string encoding the integer
  value `x` as an n-byte big-endian value
- `concat(x0, ..., xN)`: Concatenation of byte strings.
  `concat(0x01, 0x0203, 0x040506) = 0x010203040506`
- `zero(n)`: An all-zero byte string of length `n` bytes. `zero(4) =
  0x00000000`
- `xor(a,b)`: XOR of byte strings; `xor(0xF0F0, 0x1234) = 0xE2C4`.
  It is an error to call this function with two arguments of unequal
  length.

# Cryptographic Dependencies

HPKE variants rely on the following primitives:

* A Key Encapsulation Mechanism (KEM):
  - GenerateKeyPair(): Generate a key pair (sk, pk)
  - Marshal(pk): Produce a fixed-length byte string encoding the
    public key `pk`
  - Unmarshal(enc): Parse a fixed-length byte string to recover a
    public key
  - Encap(pk): Generate an ephemeral, fixed-length symmetric key and
    a fixed-length encapsulation of that key that can be decapsulated
    by the holder of the private key corresponding to pk
  - Decap(enc, sk): Use the private key `sk` to recover the ephemeral
    symmetric key from its encapsulated representation `enc`
  - AuthEncap(pkR, skS) (optional): Same as Encap(), but the outputs
    encode an assurance that the ephemeral shared key is known only
    to the holder of the private key `skS`
  - AuthDecap(skR, pkS) (optional): Same as Decap(), but the holder
    of the private key `skR` is assured that the ephemeral shared
    key is known only to the holder of the private key corresponding
    to `pkS`
  - Nzz: The length in bytes of a shared secret produced by this KEM
  - Nenc: The length in bytes of an encapsulated key produced by this KEM
  - Npk: The length in bytes of an encoded public key for this KEM

* A Key Derivation Function (KDF):
  - Extract(salt, IKM): Extract a pseudorandom key of fixed length `Nh` bytes
    from input keying material `IKM` and an optional byte string
    `salt`
  - Expand(PRK, info, L): Expand a pseudorandom key `PRK` using
    optional string `info` into `L` bytes of output keying material
  - Nh: The output size of the Extract function in bytes

* An AEAD encryption algorithm {{!RFC5116}}:
  - Seal(key, nonce, aad, pt): Encrypt and authenticate plaintext
    `pt` with associated data `aad` using secret key `key` and nonce
    `nonce`, yielding ciphertext and tag `ct`
  - Open(key, nonce, aad, ct): Decrypt ciphertext `ct` using
    associated data `aad` with secret key `key` and nonce `nonce`,
    returning plaintext message `pt` or the error value `OpenError`
  - Nk: The length in bytes of a key for this algorithm
  - Nn: The length in bytes of a nonce for this algorithm

A set of algorithm identifiers for concrete instantiations of these
primitives is provided in {{ciphersuites}}.  Algorithm identifier
values are two bytes long.

The following two functions are defined for a KDF to facilitate domain
separation of calls as well as context binding:

~~~
def LabeledExtract(salt, label, IKM):
  labeledIKM = concat("RFCXXXX ", label, IKM)
  return Extract(salt, labeledIKM)

def LabeledExpand(PRK, label, info, L):
  labeledInfo = concat(encode_big_endian(L, 2),
                        "RFCXXXX ", label, info)
  return Expand(PRK, labeledInfo, L)
~~~
\[\[RFC editor: please change "RFCXXXX" to the correct number before publication.]]

## DH-Based KEM

Suppose we are given a KDF, and a Diffie-Hellman group providing the
following operations:

- GenerateKeyPair(): Generate an ephemeral key pair `(sk, pk)`
  for the DH group in use
- DH(sk, pk): Perform a non-interactive DH exchange using the
  private key sk and public key pk to produce a Diffie-Hellman
  shared secret of length Ndh
- Marshal(pk): Produce a byte string of length Npk
  encoding the public key `pk`
- Unmarshal(enc): Parse a byte string of length Npk to recover a
  public key
- Ndh: The length in bytes of a Diffie-Hellman shared secret produced
  by the DH function of this KEM.

Then we can construct a KEM called `DHKEM(Group, KDF)` in the
following way, where `Group` denotes the Diffie-Hellman group and
`KDF` the KDF:

~~~
def ExtractAndExpand(dh, kemContext):
  prk = LabeledExtract(zero(Nh), "dh", dh)
  return LabeledExpand(prk, "prk", kemContext, Nzz)

def Encap(pkR):
  skE, pkE = GenerateKeyPair()
  dh = DH(skE, pkR)
  enc = Marshal(pkE)

  pkRm = Marshal(pkR)
  kemContext = concat(enc, pkRm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz, enc

def Decap(enc, skR):
  pkE = Unmarshal(enc)
  dh = DH(skR, pkE)

  pkRm = Marshal(pk(skR))
  kemContext = concat(enc, pkRm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz, enc

def AuthEncap(pkR, skS):
  skE, pkE = GenerateKeyPair()
  dh = concat(DH(skE, pkR), DH(skS, pkR))
  enc = Marshal(pkE)

  pkRm = Marshal(pkR)
  pkSm = Marshal(pk(skS))
  kemContext = concat(enc, pkRm, pkSm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz, enc

def AuthDecap(enc, skR, pkS):
  pkE = Unmarshal(enc)
  dh = concat(DH(skR, pkE), DH(skR, pkS))

  pkRm = Marshal(pk(skR))
  pkSm = Marshal(pkS)
  kemContext = concat(enc, pkRm, pkSm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz, enc
~~~

The KDF used in DHKEM can be equal to or different from the KDF used
in the remainder of HPKE, depending on the chosen variant.
Implementations MUST make sure to use the constants (Nh) and function
calls (LabeledExtract, LabeledExpand) of the appropriate KDF when
implementing DHKEM. See {{kdf-choice}} for a comment on the choice of
a KDF for the remainder of HPKE, and {{domain-separation}} for the
rationale of the labels.

For the variants of DHKEM defined in this document, Ndh is equal to Npk,
and the output length of the KDF's Extract function is Nzz bytes.

The GenerateKeyPair, Marshal, and Unmarshal functions are the same
as for the underlying DH group.  The Marshal functions for the
curves referenced in {#ciphersuites} are as follows:

* P-256: A single byte set to 4, followed by the X-coordinate and the
  Y-coordinate of the point, encoded as 32-byte big-endian integers
* P-384: A single byte set to 4, followed by the X-coordinate and the
  Y-coordinate of the point, encoded as 48-byte big-endian integers
* P-521: A single byte set to 4, followed by the X-coordinate and the
  Y-coordinate of the point, encoded as 66-byte big-endian integers
* Curve25519: The standard 32-byte representation of the public key
* Curve448: The standard 56-byte representation of the public key

Senders and recipients MUST validate KEM inputs and outputs as described
in {{kem-ids}}.

# Hybrid Public Key Encryption

In this section, we define a few HPKE variants.  All variants take a
recipient public key and a sequence of plaintexts `pt`, and produce an
encapsulated key `enc` and a sequence of ciphertexts `ct`.  These outputs are
constructed so that only the holder of the private key corresponding
to `pkR` can decapsulate the key from `enc` and decrypt the
ciphertexts.  All of the algorithms also take an `info` parameter
that can be used to influence the generation of keys (e.g., to fold
in identity information) and an `aad` parameter that provides
Additional Authenticated Data to the AEAD algorithm in use.

In addition to the base case of encrypting to a public key, we
include two authenticated variants, one of which authenticates
possession of a pre-shared key, and one of which authenticates
possession of a KEM private key.  The following one-byte values
will be used to distinguish between modes:

| Mode          | Value |
|:==============|:======|
| mode_base     | 0x00  |
| mode_psk      | 0x01  |
| mode_auth     | 0x02  |
| mode_auth_psk | 0x03  |

All of these cases follow the same basic two-step pattern:

1. Set up an encryption context that is shared between the sender
   and the recipient
2. Use that context to encrypt or decrypt content

A "context" encodes the AEAD algorithm and key in use, and manages
the nonces used so that the same nonce is not used with multiple
plaintexts.

The constructions described here presume that the relevant non-private
parameters (`enc`, `pskID`, etc.) are transported between the sender and the
recipient by some application making use of HPKE.

The procedures described in this session are laid out in a
Python-like pseudocode.  The algorithms in use are left implicit.

## Creating the Encryption Context

The variants of HPKE defined in this document share a common
key schedule that translates the protocol inputs into an encryption
context. The key schedule inputs are as follows:

* `zz` - A shared secret generated via the KEM for this transaction
* `info` - Application-supplied information (optional; default value
  "")
* `psk` - A pre-shared secret held by both the sender
  and the recipient (optional; default value `zero(Nh)`).
* `pskID` - An identifier for the PSK (optional; default value `zero(0)`)
* `pkSm` - The sender's encoded public key (optional; default
  value `zero(Npk)`)

Senders and recipients MUST validate KEM inputs and outputs as described
in {{kem-ids}}.

The `psk` and `pskID` fields MUST appear together or not at all.
That is, if a non-default value is provided for one of them, then
the other MUST be set to a non-default value.

The key and nonce computed by this algorithm have the property that
they are only known to the holder of the recipient private key, and
the party that ran the KEM to generate `zz` and `enc`.  If the `psk`
and `pskID` arguments are provided, then the recipient is assured
that the sender held the PSK.  If the `pkSm` argument is
provided, then the recipient is assumed that the sender held the
corresponding private key (assuming that `zz` and `enc` were
generated using the AuthEncap / AuthDecap methods; see below).

The HPKE algorithm identifiers, i.e., the KEM `kem_id`, KDF `kdf_id`, and
AEAD `aead_id` 2-byte code points, are assumed implicit from the
implementation and not passed as parameters.

~~~~~
default_pkSm = zero(Npk)
default_psk = zero(Nh)
default_pskID = zero(0)

def VerifyMode(mode, psk, pskID, pkSm):
  got_psk = (psk != default_psk and pskID != default_pskID)
  no_psk = (psk == default_psk and pskID == default_pskID)
  got_pkSm = (pkSm != default_pkSm)
  no_pkSm = (pkSm == default_pkSm)

  if mode == mode_base and (got_psk or got_pkSm):
    raise Exception("Invalid configuration for mode_base")
  if mode == mode_psk and (no_psk or got_pkSm):
    raise Exception("Invalid configuration for mode_psk")
  if mode == mode_auth and (got_psk or no_pkSm):
    raise Exception("Invalid configuration for mode_auth")
  if mode == mode_auth_psk and (no_psk or no_pkSm):
    raise Exception("Invalid configuration for mode_auth_psk")

def KeySchedule(mode, zz, info, psk, pskID, pkSm):
  VerifyMode(mode, psk, pskID, pkSm)

  ciphersuite = concat(encode_big_endian(kem_id, 2),
                       encode_big_endian(kdf_id, 2),
                       encode_big_endian(aead_id, 2))
  pskID_hash = LabeledExtract(zero(Nh), "pskID", pskID)
  info_hash = LabeledExtract(zero(Nh), "info", info)
  context = concat(ciphersuite, mode, pskID_hash, info_hash)

  psk = LabeledExtract(zero(Nh), "psk", psk)

  secret = LabeledExtract(psk, "zz", zz)
  key = LabeledExpand(secret, "key", context, Nk)
  nonce = LabeledExpand(secret, "nonce", context, Nn)
  exporter_secret = LabeledExpand(secret, "exp", context, Nh)

  return Context(key, nonce, exporter_secret)
~~~~~

Note that the context construction in the KeySchedule procedure is
equivalent to serializing a structure of the following form in the
TLS presentation syntax:

~~~~~
struct {
    uint16 kem_id;
    uint16 kdf_id;
    uint16 aead_id;
    uint8 mode;
    opaque pskID_hash[Nh];
    opaque info_hash[Nh];
} HPKEContext;
~~~~~

### Encryption to a Public Key {#hpke-kem}

The most basic function of an HPKE scheme is to enable encryption
for the holder of a given KEM private key.  The `SetupBaseS()` and
`SetupBaseR()` procedures establish contexts that can be used to
encrypt and decrypt, respectively, for a given private key.

The shared secret produced by the KEM is combined via the KDF
with information describing the key exchange, as well as the
explicit `info` parameter provided by the caller.

~~~~~
def SetupBaseS(pkR, info):
  zz, enc = Encap(pkR)
  return enc, KeySchedule(mode_base, zz, info,
                          default_psk, default_pskID, default_pkSm)

def SetupBaseR(enc, skR, info):
  zz = Decap(enc, skR)
  return KeySchedule(mode_base, zz, info,
                     default_psk, default_pskID, default_pkSm)
~~~~~

### Authentication using a Pre-Shared Key {#mode-psk}

This variant extends the base mechanism by allowing the recipient
to authenticate that the sender possessed a given pre-shared key
(PSK).  We assume that both parties have been provisioned with both
the PSK value `psk` and another byte string `pskID` that is used to
identify which PSK should be used.

The primary differences from the base case are:

* The PSK is used as the `salt` input to the KDF (instead of 0)
* The PSK ID is added to the context string used as the `info` input
  to the KDF

The PSK SHOULD be of length Nh bytes or longer, and SHOULD have
Nh bytes of entropy or more. See {{security-psk}} for a more detailed
discussion.

~~~~~
def SetupPSKS(pkR, info, psk, pskID):
  zz, enc = Encap(pkR)
  return enc, KeySchedule(mode_psk, zz, info, psk, pskID, default_pkSm)

def SetupPSKR(enc, skR, info, psk, pskID):
  zz = Decap(enc, skR)
  return KeySchedule(mode_psk, zz, info, psk, pskID, default_pkSm)
~~~~~

### Authentication using an Asymmetric Key {#mode-auth}

This variant extends the base mechanism by allowing the recipient
to authenticate that the sender possessed a given KEM private key.
This assurance is based on the assumption that
`AuthDecap(enc, skR, pkS)` produces the correct shared secret
only if the encapsulated value `enc` was produced by
`AuthEncap(pkR, skS)`, where `skS` is the private key corresponding
to `pkS`.  In other words, only two people could have produced this
secret, so if the recipient is one, then the sender must be the
other.

The primary differences from the base case are:

* The calls to `Encap` and `Decap` are replaced with calls to
  `AuthEncap` and `AuthDecap`.
* The sender public key is added to the context string

Obviously, this variant can only be used with a KEM that provides
`AuthEncap()` and `AuthDecap()` procedures.

This mechanism authenticates only the key pair of the sender, not
any other identity.  If an application wishes to authenticate some
other identity for the sender (e.g., an email address or domain
name), then this identity should be included in the `info` parameter
to avoid unknown key share attacks.

~~~~~
def SetupAuthS(pkR, info, skS):
  zz, enc = AuthEncap(pkR, skS)
  return enc, KeySchedule(mode_auth, zz, info, default_psk, default_pskID, pkSm)

def SetupAuthR(enc, skR, info, pkS):
  zz = AuthDecap(enc, skR, pkS)
  return KeySchedule(mode_auth, zz, info, default_psk, default_pskID, pkSm)
~~~~~

### Authentication using both a PSK and an Asymmetric Key {#mode-auth-psk}

This mode is a straightforward combination of the PSK and
authenticated modes.  The PSK is passed through to the key schedule
as in the former, and as in the latter, we use the authenticated KEM
variants.

~~~~~
def SetupAuthPSKS(pkR, info, psk, pskID, skS):
  zz, enc = AuthEncap(pkR, skS)
  return enc, KeySchedule(mode_auth_psk, zz, info, psk, pskID, pkSm)

def SetupAuthPSKR(enc, skR, info, psk, pskID, pkS):
  zz = AuthDecap(enc, skR, pkS)
  return KeySchedule(mode_auth_psk, zz, info, psk, pskID, pkSm)
~~~~~

The PSK SHOULD be of length Nh bytes or longer, and SHOULD have
Nh bytes of entropy or more. See {{security-psk}} for a more detailed
discussion.

## Encryption and Decryption {#hpke-dem}

HPKE allows multiple encryption operations to be done based on a
given setup transaction.  Since the public-key operations involved
in setup are typically more expensive than symmetric encryption or
decryption, this allows applications to "amortize" the cost of the
public-key operations, reducing the overall overhead.

In order to avoid nonce reuse, however, this decryption must be
stateful. Each of the setup procedures above produces a context object
that stores the required state:

* The AEAD algorithm in use
* The key to be used with the AEAD algorithm
* A base nonce value
* A sequence number (initially 0)

All of these fields except the sequence number are constant.  The
sequence number is used to provide nonce uniqueness: The nonce used
for each encryption or decryption operation is the result of XORing
the base nonce with the current sequence number, encoded as a
big-endian integer of the same length as the nonce.  Implementations
MAY use a sequence number that is shorter than the nonce (padding on
the left with zero), but MUST return an error if the sequence number
overflows.

Encryption is unidirectional from sender to recipient. Each encryption
or decryption operation increments the sequence number for the context
in use.  The sender's context MUST be used for encryption only. Similarly,
the recipient's context MUST be used for decryption only. Higher-level
protocols re-using the HPKE key exchange for more general purposes can
derive separate keying material as needed using use the Export interface;
see {{hpke-export}} for more details.

It is up to the application to ensure that encryptions and
decryptions are done in the proper sequence, so that encryption
and decryption nonces align. If a Seal or Open operation would cause the `seq`
field to wrap, then the implementation MUST return an error.

~~~~~
def Context.Nonce(seq):
  encSeq = encode_big_endian(seq, Nn)
  return xor(self.nonce, encSeq)

def Context.IncrementSeq():
  if self.seq >= (1 << Nn) - 1:
    return NonceOverflowError
  self.seq += 1

def Context.Seal(aad, pt):
  ct = Seal(self.key, self.Nonce(self.seq), aad, pt)
  self.IncrementSeq()
  return ct

def Context.Open(aad, ct):
  pt = Open(self.key, self.Nonce(self.seq), aad, ct)
  if pt == OpenError:
    return OpenError
  self.IncrementSeq()
  return pt
~~~~~

## Secret Export {#hpke-export}

HPKE provides a interface for exporting secrets from the encryption Context, similar
to the TLS 1.3 exporter interface (See {{?RFC8446}}, Section 7.5). This interface takes as
input a context string `exporter_context` and desired length `L` (in bytes), and produces
a secret derived from the internal exporter secret using the corresponding KDF Expand
function.

~~~~~
def Context.Export(exporter_context, L):
  return LabeledExpand(self.exporter_secret, "sec", exporter_context, L)
~~~~~

# Single-Shot APIs

In many cases, applications encrypt only a single message to a recipient's public key.
This section provides templates for HPKE APIs that implement stateless "single-shot" encryption
and decryption using APIs specified in {{hpke-kem}} and {{hpke-dem}}:

~~~~~
def Seal<MODE>(pkR, info, aad, pt, ...):
  enc, ctx = Setup<MODE>I(pkR, info, ...)
  ct = ctx.Seal(aad, pt)
  return enc, ct

def Open<MODE>(enc, skR, info, aad, ct, ...):
  ctx = Setup<MODE>R(enc, skR, info, ...)
  return ctx.Open(aad, ct)
~~~~~

The `MODE` template parameter is one of Base, PSK, Auth, or AuthPSK. The optional parameters
indicated by "..."" depend on `MODE` and may be empty. SetupBase, for example, has no
additional parameters. Thus, SealAuthPSK and OpenAuthPSK would be implemented as follows:

~~~
def SealAuthPSK(pkR, info, aad, pt, psk, pskID, skS):
  enc, ctx = SetupAuthPSKS(pkR, info, psk, pskID, skS)
  ct = ctx.Seal(aad, pt)
  return enc, ct

def OpenAuthPSK(enc, skR, info, aad, ct, psk, pskID, pkS):
  ctx = SetupAuthPSKR(enc, skR, info, psk, pskID, pkS)
  return ctx.Open(aad, ct)
~~~

# Algorithm Identifiers {#ciphersuites}

## Key Encapsulation Mechanisms (KEMs) {#kem-ids}

| Value  | KEM                            | Nzz  | Nenc | Npk | Reference                    |
|:-------|:-------------------------------|:-----|:-----|:----|:-----------------------------|
| 0x0000 | (reserved)                     | N/A  | N/A  | N/A | N/A                          |
| 0x0010 | DHKEM(P-256, HKDF-SHA256)      | 32   | 65   | 65  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0011 | DHKEM(P-384, HKDF-SHA384)      | 48   | 97   | 97  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0012 | DHKEM(P-521, HKDF-SHA512)      | 64   | 133  | 133 | {{NISTCurves}}, {{?RFC5869}} |
| 0x0020 | DHKEM(Curve25519, HKDF-SHA256) | 32   | 32   | 32  | {{?RFC7748}}, {{?RFC5869}}   |
| 0x0021 | DHKEM(Curve448, HKDF-SHA512)   | 64   | 56   | 56  | {{?RFC7748}}, {{?RFC5869}}   |

### Marshal

For the NIST curves P-256, P-384 and P-521, the Marshal function of the
DH scheme produces the normal (non-compressed) representation of the
public key, according to {{SECG}}.

For the CFRG curves Curve25519 and Curve448, the Marshal function is
the identity function, since these curves already use fixed-length
byte strings for public keys.

### Validation of Inputs and Outputs

The following public keys are subject to validation if the curve
requires public key validation: the sender MUST validate the recipient's
public key `pkR`; the recipient MUST validate the ephemeral public key
`pkE`; in authenticated modes, the recipient MUST validate the sender's
static public key `pkS`.

For the NIST curves P-256, P-384 and P-521, senders and recipients
MUST perform full public-key validation on all public key inputs as
defined in {{keyagreement}}, which includes validating that a public
key is on the curve and part of the correct prime-order subgroup.
Additionally, one of the following checks MUST be ensured: the scalar
given as input to DH is in the interval [1, n-1] where n is the prime
order of the subgroup; the result of DH is not the point at infinity.

For the CFRG curves Curve25519 and Curve448, validation of public keys
is not required. Senders and recipients MUST check whether the shared
secret is the all-zero value and abort if so, as described in
{{?RFC7748}}.

## Key Derivation Functions (KDFs) {#kdf-ids}

| Value  | KDF         | Nh  | Reference    |
|:-------|:------------|-----|:-------------|
| 0x0000 | (reserved)  | N/A | N/A          |
| 0x0001 | HKDF-SHA256 | 32  | {{?RFC5869}} |
| 0x0002 | HKDF-SHA384 | 48  | {{?RFC5869}} |
| 0x0003 | HKDF-SHA512 | 64  | {{?RFC5869}} |

## Authenticated Encryption with Associated Data (AEAD) Functions {#aead-ids}

| Value  | AEAD             | Nk  | Nn  | Reference    |
|:-------|:-----------------|:----|:----|:-------------|
| 0x0000 | (reserved)       | N/A | N/A | N/A          |
| 0x0001 | AES-GCM-128      | 16  | 12  | {{GCM}}      |
| 0x0002 | AES-GCM-256      | 32  | 12  | {{GCM}}      |
| 0x0003 | ChaCha20Poly1305 | 32  | 12  | {{?RFC8439}} |

# Security Considerations {#sec-considerations}

## Security Properties {#sec-properties}

HPKE has several security goals, depending on the mode of operation,
against active and adaptive attackers that can compromise partial
secrets of senders and recipients. The desired security goals are
detailed below:

- Message secrecy: Privacy of the sender's messages, i.e., IND-CCA2
security
- Export key secrecy: Indistinguishability of each export
secret from a uniformly random bitstring of equal length
- Sender authentication: Proof of sender origin for Auth and AuthPSK
modes

It is shown in {{CS01}} that a hybrid scheme of essentially the same
form described here is IND-CCA2-secure as long as the the underlying KEM
and AEAD schemes are IND-CCA2-secure.  The main difference between the
scheme proposed there and the scheme in this document (both named HPKE)
is that we interpose some KDF calls between the KEM and
the AEAD.  So further analysis is needed on two fronts, first to verify
that the additional KDF calls do not cause the IND-CCA2 property to
fail, and second to verify the two additional properties noted above.

This work has been done for the case where the KEM is DHKEM, the AEAD is
any IND-CCA2 scheme, and the DH group and KDF satisfy the following
conditions:

- DH group: The gap Diffie-Hellman (GDH) problem is hard {{GAP}}.
- Extract and Expand (in DHKEM): Extract is indifferentiable from a
  random oracle. Expand is a pseudorandom function, wherein the first
  argument is the key.
- Extract and Expand (elsewhere): Extract is indifferentiable from a
  random oracle. Expand is a pseudorandom function, wherein the first
  argument is the key.

In particular, the KDFs and DH groups defined in this document (see
{{kdf-ids}} and {{kem-ids}}) satisfy these properties.

The analysis in {{HPKEAnalysis}} demonstrates that under these
constraints, HPKE continues to provide IND-CCA2 security, and provides
the additional properties noted above.  The analysis considers two
variants of HPKE usage: single-shot message encryption and secret key
export. In the single-shot variant, S uses the single-shot API to use
the key once to encrypt a plaintext. The export variant is the same as
single-shot variant, except that the sender additionally exports two
independent secrets using the secret export interface. We distinguish
these two variants because the single-shot API does not lend itself to
use the Export interface.

The table below summarizes the main results from {{HPKEAnalysis}}. N/A
means that a property does not apply for the given mode, whereas X means
the given mode satisfies the property.

| Variant              | Message Sec. | Export Sec. | Sender Auth. |
|:---------------------|:------------:|:-----------:|:------------:|
| Base, single-shot    | X            | N/A         | N/A          |
| PSK, single-shot     | X            | N/A         | X            |
| Auth, single-shot    | X            | N/A         | X            |
| AuthPSK, single-shot | X            | N/A         | X            |
| Base, export         | X            | X           | N/A          |
| PSK, export          | X            | X           | X            |
| Auth, export         | X            | X           | X            |
| AuthPSK, export      | X            | X           | X            |

If non-DH-based KEM schemes are to be used with HPKE, further analysis
will be necessary to prove their security.  The results from {{CS01}}
provide some indication that any IND-CCA2 KEM will suffice here, but are
not conclusive given the difference in schemes.

In addition, both {{CS01}} and {{HPKEAnalysis}} are premised on classical
security models and assumptions, and do not consider attackers capable of quantum
computation. A full proof of post-quantum security would need to take this
difference into account, in addition to simply using a post-quantum KEM.

## Security Requirements on a KEM used within HPKE

A KEM used within HPKE MUST ensure the following to avoid identity
mis-binding issues: The shared secret computed by Encap and Decap MUST
depend explicitly on the KEM public key pkR and the KEM ciphertext enc.
The shared secret returned by AuthEncap and AuthDecap MUST explicitly
depend on the KEM public keys pkR and pkS and the KEM ciphertext enc.
This is usually implemented by including these values explicitly into
the context of the key derivation function used to compute the shared
secret. This is also how DHKEM meets the requirement.

## Security Requirements on a KDF {#kdf-choice}

The choice of the KDF for the remainder of HPKE should be made based on
the security level provided by the KEM and, if applicable, by the PSK.
The KDF SHOULD have at least have the security level of the KEM and
SHOULD at least have the security level provided by the PSK.

HPKE's KeySchedule uses LabeledExtract to convert an arbitrary-length
PSK into a fixed-length PSK. This is necessary because of the
restrictions on the key in HMAC's indifferentiability theorem {{HMAC}}.
A future instantiation of HPKE MAY omit this line if: Extract is not
instantiated by HKDF-Extract and there is an indifferentiability theorem
for Extract without restriction on the key's length.

## Pre-Shared Key Recommendations {#security-psk}

In the PSK and AuthPSK modes, the PSK SHOULD be of length Nh bytes or
longer, and SHOULD have Nh bytes of entropy or more. Using a PSK shorter
than Nh bytes is permitted. A PSK that is longer than Nh bytes or that
has more than Nh bytes of entropy, respectively, does not increase the
security level of HPKE, because the extraction step involving the PSK
only outputs Nh bytes.

HPKE is specified to use HKDF as key derivation function. HKDF is not
designed to slow down dictionary attacks, see {{?RFC5869}}. Thus, HPKE's
PSK mechanism is not suitable for use with a low-entropy password as the
PSK: in scenarios in which the adversary knows the KEM shared secret zz
and has access to an oracle that allows to distinguish between a good
and a wrong PSK, it can perform a dictionary attack on the PSK. This
oracle can be the decryption operation on a captured HPKE ciphertext or
any other recipient behavior which is observably different when using a
wrong PSK. The adversary knows the KEM shared secret zz if it knows all
KEM private keys of one participant. In the PSK mode this is trivially
the case if the adversary acts as sender.

## Domain Separation {#domain-separation}

HPKE allows combining a DHKEM variant DHKEM(Group, KDF') and a KDF
such that both KDFs are instantiated by the same KDF. By design, the
calls to Extract and Expand inside DHKEM and the remainder of HPKE have
different prefix-free encodings for the second parameter. This is
achieved by the different prefix-free label parameters in the calls to
LabeledExtract and LabeledExpand. This serves to separate the input
domains of all Extract and Expand invocations. It also justifies modeling
them as independent functions even if instantiated by the same KDF.

Future KEM instantiations MUST ensure that all internal invocations of
Extract and Expand can be modeled as functions independent from the
invocations of Extract and Expand in the remainder of HPKE. One way to
ensure this is by using an equal or similar prefixing scheme with
an identifier different from "RFCXXXX ". Particular attention needs to
be paid if the KEM directly invokes functions that are used internally
in HPKE's Extract or Expand, such as Hash and HMAC in the case of HKDF.
It MUST be ensured that inputs to these invocations cannot collide with
inputs to the internal invocations of these functions inside Extract or
Expand. In HPKE's KeySchedule this is avoided by using Extract instead of
Hash on the arbitrary-length inputs `info`, `pskID`, and `psk`.

The string literal "RFCXXXX" used in LabeledExtract and LabeledExpand
ensures that any secrets derived in HPKE are bound to the scheme's name,
even when possibly derived from the same Diffie-Hellman or KEM shared
secret as in another scheme.

## External Requirements / Non-Goals

HPKE is designed to be a fairly low-level primitive, and thus does not provide
several features that a more high-level protocol might provide, for example:

* Downgrade prevention - HPKE assumes that the sender and recipient agree on
  what algorithms to use.  Depending on how these algorithms are negotiated, it
  may be possible for an intermediary to force the two parties to use
  suboptimal algorithms.

* Replay protection - The requirement that ciphertexts be presented to the
  Context.Open function in the same order they were generated by Context.Seal
  provides a degree of replay protection within a stream of ciphertexts
  resulting from a given Context.  HPKE provides no other replay protection.

* Forward secrecy - HPKE ciphertexts are not forward-secure. In mode_base
  and mode_auth, a given ciphertext can be decrypted if the recipient's public
  encryption key is compromised. In mode_psk and mode_auth_psk, a given
  ciphertext can be decrypted if the recipient's public encryption key and the
  PSK are compromised.

## Metadata Protection

The authenticated modes of HPKE (PSK, Auth, AuthPSK) require that the recipient
know what key material to use for the sender.  This can be signaled in
applications by sending the PSK ID (`pskID` above) and/or the sender's public
key (`pkS`).  However, these values themselves might be considered sensitive,
since in a given application context, they might identify the sender.

An application that wishes to protect these metadata values without requiring
further provisioning of keys can use an additional instance of HPKE, using the
unauthenticated base mode.  Where the application might have sent `(pskID, pkS,
enc, ciphertext)` before, it would now send (enc2, ciphertext2, enc, ciphertext),
where `(enc2, ciphertext2)` represent the encryption of the `pskID` and `pkS`
values.

The cost of this approach is an additional KEM operation each for the sender and
the recipient.  A potential lower-cost approach (involving only symmetric
operations) would be available if the nonce-protection schemes in {{BNT19}}
could be extended to cover other metadata.  However, this construction would
require further analysis.

## Designated-Verifier Signature

The Auth and AuthPSK modes HPKE can be used to construct a lightweight
"designated-verifier signature" scheme {{JKR96}}, in the sense that the message
is authenticated as coming from the sender, but the only party who can verify
the authentication is the recipient (the holder of `skR`).

To create such a signature, the sender simply performs a normal HPKE setup in
the proper mode, and calls the Seal method on the resulting context with an
empty plaintext value and the content to be signed as AAD.  This produces an
encoded key `enc` and a ciphertext value that contains only the AAD tag.

For example, using DHKEM-X25519 and AES-128-GCM, this would produce a 48-byte
signature comprising a 32-byte ephemeral X25519 key and a 16-byte GCM tag.

To verify such a signature, the recipient performs the corresponding HPKE setup
and calls Open with the provided ciphertext.  If the AEAD authentication passes,
then the signature is valid.

This scheme re-uses the authentication scheme underlying the AEAD algorithm in
use, while using the KEM to establish a one-time authentication key from a pair
of KEM public keys.

# Message Encoding

This document does not specify a wire format encoding for HPKE messages. Applications
that adopt HPKE must therefore specify an unambiguous encoding mechanism which includes,
minimally: the encapsulated value `enc`, ciphertext value(s) (and order if there are
multiple), and any info values that are not implicit.

# IANA Considerations

This document requests the creation of three new IANA registries:

* HPKE KEM Identifiers
* HPKE KDF Identifiers
* HPKE AEAD Identifiers

All of these registries should be under a heading of "Hybrid Public Key
Encryption", and administered under a Specification Required policy {{!RFC8126}}

## KEM Identifiers

The "HPKE KEM Identifiers" registry lists identifiers for key encapsulation
algorithms defined for use with HPKE.  These are two-byte values, so the
maximum possible value is 0xFFFF = 65535.

Template:

* Value: The two-byte identifier for the algorithm
* KEM: The name of the algorithm
* Nzz: The length in bytes of a shared secret produced by the algorithm
* Nenc: The length in bytes of an encapsulated key produced by the algorithm
* Npk: The length in bytes of an encoded public key for the algorithm
* Reference: Where this algorithm is defined

Initial contents: Provided in {{kem-ids}}

## KDF Identifiers

The "HPKE KDF Identifiers" registry lists identifiers for key derivation
functions defined for use with HPKE.  These are two-byte values, so the maximum
possible value is 0xFFFF = 65535.

Template:

* Value: The two-byte identifier for the algorithm
* KDF: The name of the algorithm
* Nh: The output size of the Extract function in bytes
* Reference: Where this algorithm is defined

Initial contents: Provided in {{kdf-ids}}

## AEAD Identifiers

The "HPKE AEAD Identifiers" registry lists identifiers for authenticated
encryption with associated data (AEAD) algorithms defined for use with HPKE.
These are two-byte values, so the maximum possible value is 0xFFFF = 65535.

Template:

* Value: The two-byte identifier for the algorithm
* AEAD: The name of the algorithm
* Nk: The length in bytes of a key for this algorithm
* Nn: The length in bytes of a nonce for this algorithm
* Reference: Where this algorithm is defined

Initial contents: Provided in {{aead-ids}}

--- back

# Test Vectors

These test vectors are also available in JSON format at {{TestVectors}}.

## DHKEM(Curve25519, HKDF-SHA256), HKDF-SHA256, AES-GCM-128

### Base Setup Information
~~~
mode: 0
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 3499ae19fbc3027d6f2352eccd86c18164d059f3c11a8ac8aa49756161ced6b5
skE: 47214df7da1f22871dd17388776b8469cf356c98f44b395968017f025e133f5a
pkR: 91fd1d21d98e26dc390ad9eb4519d4a3379f7085e63e56209263cc334b674a3c
pkE: 1b427849d633e931579a4dea4f2dbb4ac45414f2161b4d83b03b232a590fa35a
enc: 1b427849d633e931579a4dea4f2dbb4ac45414f2161b4d83b03b232a590fa35a
zz: 98eac6ebcbb1a187a3a0248d1df0605c3f4621a17724db1782a00be31e63ef04
context: 002000010001007c06ab49234d271ba849bf112283c4e965da8969454eebfc7
187029d62893ed59e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 98687fb837f993f2fd86b0b9c53ec4cff9773a321e1f8d79b137ca0bcff36318
key: f1fb08aa4643c7f6b64af99d287721f0
nonce: 61e43b7bc47a4a85dbf25bbb
exporterSecret:
c9a6c45426ec26c5b2e1664c6b85fd2fae319ab905c4eec4957bfa8ed0a65e37
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 61e43b7bc47a4a85dbf25bbb
ciphertext: 31619e286b0a7b17f771faaf797d758db61b04fb3313810bf1de36238bb3
38d6d29c9e18e68fe4dbbd846eeb6f

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 61e43b7bc47a4a85dbf25bba
ciphertext: 020e870bcf1c9f2d907ea1434b4659feec38dc8926c79529d282780df6c0
260fbbf20dbb6f7b68acf29e461b77

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 61e43b7bc47a4a85dbf25bb9
ciphertext: 6ad488577173da0b3dd93aebb3f2e16738e63c2bd5c78ba33ff2426cc01b
b4f46685ba0e414a6134f80d532fbb

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 61e43b7bc47a4a85dbf25bbf
ciphertext: dddfe41f94d2c70875a148c5a4f678d68968e4519b4c5a13430c0f9a93ec
642d857c47970f50933769e9775091

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 3d0eca436e1627874175fa1ab61524b13c7251f9978be8e5c693ee04c55162d9
skE: d242dbeb9067c95a41eb644036f235c35c366799981ff4916a7b80f607142c12
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 534016e0c9d7080af39020802b355a4115d4cb183accf517a8a044cde605152d
pkE: e518a83ad1f1c1ba70ddeac8fee0eb931191242e859e0f8363cc369d09329673
enc: e518a83ad1f1c1ba70ddeac8fee0eb931191242e859e0f8363cc369d09329673
zz: 34119438bfd8a6f843f14428f6c172e12b6256469a9ec8b1e3dea762ad4acb70
context: 002000010001011c417ad62e7adb08b7d000c720cff8fe718eca97fabf4237f
2779a2b6d013a389e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 544def0c2378694b1f7c276f0a3f5b467d32c4247c821fd36435b221efd261d8
key: b2cbf86e1c0a65ccd0d64f8ba0f457c9
nonce: e199588bd00148104cd28222
exporterSecret:
84ce1ded09f0217f7723e84188a7704b4be5ec165899c2f6213d469a5c96bbd8
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: e199588bd00148104cd28222
ciphertext: 6a93f4d2b7af57f1dbf79d2b4b4be334aa5c8056e5e9f154bfff512ce3df
2c5f2a92aab2df2e8bf46a82ae4217

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: e199588bd00148104cd28223
ciphertext: 3a4c95ac44663f8dbc3e6c32f6bbd404cb5641c281b59bf0bfe63538594a
18305b5022382a4e3c1627290787a8

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: e199588bd00148104cd28220
ciphertext: 639b0df828ec60c71d34770bd13094588fb6bdd8c6f3059e9468838810a3
585b8256050bf8cfc233d29ac3ce30

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: e199588bd00148104cd28226
ciphertext: 2430aa487303fee4a1709982fbe40d86e0fae9ba4a83af53df849e8a0644
cc25d172512b9e0b64ed159dd49937

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 2574625b9c0800e89f0a4657836931f870fa29725830a08df63c7ceb609eb7d8
skS: 53cb9ef46ac38c5fce43d90bd52c4a1757fdb7f16d88b13dffa2e6bcf77120cb
skE: 1191c46d2a70d933209be942f34f28d69fd908c9c3a70533b398c079cba042a9
pkR: 636999143b1a6cf8f304c892caa8deb1d007bf8c8a722827f136f69f28b92801
pkS: c224835d134aea7b8fe7ebb6bb5321df0f8e8f6a44d818c091222d8fcea28854
pkE: c336bac032c86d441fa88e213a2034b03e6bf0b34f8c8989900e156203371a59
enc: c336bac032c86d441fa88e213a2034b03e6bf0b34f8c8989900e156203371a59
zz: 0b505c48705dac03538ab4e48b82ed74b0dd5c651ba1a847462845c2247bcd77
context: 002000010001027c06ab49234d271ba849bf112283c4e965da8969454eebfc7
187029d62893ed59e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 6e8853091885cc040ac8e379c605c51cfc9a99ef179f6a353874a078bc20c290
key: d8645763e626e2e8c029123a0a859159
nonce: a79b3531268f10d6791ba240
exporterSecret:
dbb449d02b9b9afb72af818ce04037188b5fff97d93fa0aa5b49312fd870b088
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: a79b3531268f10d6791ba240
ciphertext: 41fcb5768632141b9bb58d7536cc4c91c0099c2cdca765e98f647ec161bf
d03a93f9358bb39113a7e2d6f6a5ae

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: a79b3531268f10d6791ba241
ciphertext: 2a9b38491bfbf9b73911488183e7dcaa3aa2961617cc9a8af4cd72c43de1
3a856def87af0f90c323df37ce03e9

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: a79b3531268f10d6791ba242
ciphertext: 76d4a29fc2b5bb6076f8c0fdb6a95d9ae8b4598153bb06c5a6c627fef234
2ee26b4d4005d4874e09ef54ad7f97

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: a79b3531268f10d6791ba244
ciphertext: fbcbeb1b5ea10995b1aa7bf2c5660a4d995a90f8e20a65f8829431e4cc2f
2297e755b904b5e6518a6cc22bd697

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: b283be19e8d0581c6ce4ea2f8b0a5cb72b9cf5d421d683bbdcd5ca5d815151e9
skS: f99a17ee6429fdedc2e9eea3e248c2d0e314a63467a75d52942e35f6b4055267
skE: ea34a796bcb2f885da6b8485b60135da7d904c490573efc52fccd2574e657409
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 3c9ac60effcf7391dab79c65a927f0b7df95965686501f4d4f6227c78138e55d
pkS: ee55202c257175b505e673fa0408538e00645b66383d46fed35586b759563346
pkE: bb577eb253133ef3374f06bd5b4e9fb60fd8d1b5b685f143af5226d748815e3a
enc: bb577eb253133ef3374f06bd5b4e9fb60fd8d1b5b685f143af5226d748815e3a
zz: e08f2cc855ad1db0d8d04ec6b0aa87aefe4cbe239ae342bf797c912526cce3d7
context: 002000010001031c417ad62e7adb08b7d000c720cff8fe718eca97fabf4237f
2779a2b6d013a389e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: a99a18cd15ffbc638d731d0a2ba752f61a327f200cb2673f3599ac40ec9f6693
key: df4e5566355149359c708e4153cde759
nonce: d70a445d3dd3d9e4b0534bcf
exporterSecret:
53292c4a68b0b7ab4a18403c72d9d6dba457abdb6580a7ed49710f5cfa6e2b5f
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: d70a445d3dd3d9e4b0534bcf
ciphertext: ebbca493489e6f6be704f45f93ee821677d0afc46912e4f285c0c124dae0
3dc41a77e6b93d6565f9f6fcb90877

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: d70a445d3dd3d9e4b0534bce
ciphertext: 85ebe57606a282dc311d2c1ce95b0cdc49a151867229ec0d717ed6109327
9a16c5165eca89587fc3293161174d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: d70a445d3dd3d9e4b0534bcd
ciphertext: 91ceddca9b9f77e92056b2ebd6f01b88f61ef31ddbf58005fdbcf2006662
b297bd5df2e8439c55369d9c726430

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: d70a445d3dd3d9e4b0534bcb
ciphertext: 4201c675d1d9b1147acbbca2c12d7cdc0e49c7bc81f50069b95483602983
28c99b0dd42ae6c1a75bd2c0d1d422

~~~

## DHKEM(Curve25519, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: d5cd03340bb2dd6cb0906e77a891bcca13d283416597a95b1f7a725012b4977b
skE: 28ccb333489f687de754b833245c56df21ecacb0a54d9281546b7fd687c24cce
pkR: 7c69649e592259ec5f22a383cc356614c94e5d5a3f4406c01d83e5f4a0a31312
pkE: 2ad6d24266a75b209d13727dcba8142b896ac2e1cf70795e1f60d2fcc9379050
enc: 2ad6d24266a75b209d13727dcba8142b896ac2e1cf70795e1f60d2fcc9379050
zz: 0c3e756ecf68b8c546395f0796a0c33d15315e77188ab7afbc66ff89a43eabd5
context: 002000010003007c06ab49234d271ba849bf112283c4e965da8969454eebfc7
187029d62893ed59e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: d44fc68920226ae46a2a99ad648bb763f01e04ea5db4df89e010a15654cbb572
key: 6d5c2ea7c88959b6507ebea61f641f82b4f3314ee249f079b87c29b657ac11c2
nonce: 90e0d8d826fccfad8d024a0f
exporterSecret:
e6ae61526e2e64acdb74cbef7f8ea2ca19e4d6f393f79c1a4cab0a860bd55db3
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 90e0d8d826fccfad8d024a0f
ciphertext: 0f98fe9847b90915be47102332d8cd1855ee03811c3222260a97cf3590db
e1441e2603b48248c92ccf278ab856

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 90e0d8d826fccfad8d024a0e
ciphertext: 7fd68317f3e472236dcba13171f62d8a596d90dfd81497575cd7d803fe75
3e0712a0b9308a87a1308f1eb229f0

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 90e0d8d826fccfad8d024a0d
ciphertext: 8ca628d9e0b531398a3c3b922ea4cb43c8b3fe170c11145c80cff8ccaaab
a7af6236c5f0a457b32d8d57022553

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 90e0d8d826fccfad8d024a0b
ciphertext: d55f1b9e7c52d95d5b53af926b6584b44e0fbfc726a2a48211f12cd3a552
a5f79682921a3cb177bf412abc2853

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: b3b856b0f149672cda384ce1de37d4999b4e03d1cd5e44361b4a201964ab2fec
skE: e1b20ed580ebaa2cd14a0e860d48adef29a85d5418bd415e5ea85f350dae5569
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: daacda481201f7df293e1a160a66695fc122f5460f2b307883ada12b43deda6e
pkE: 0d1051bdf6b2e0f00677ba1001e8854ad263edd4e0ba09594cf49d68406af866
enc: 0d1051bdf6b2e0f00677ba1001e8854ad263edd4e0ba09594cf49d68406af866
zz: 3bd14b9de9458b2c8aa7b567c253dee1605ca63784f120bb77b896250e7368c6
context: 002000010003011c417ad62e7adb08b7d000c720cff8fe718eca97fabf4237f
2779a2b6d013a389e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: f955b092d6187bc86b612abebbb399ffc0a4f5b930f7cb6d46e2daa98810cb7a
key: f01193de430779de6574d795d266fed7d89b9d598c5f6d34082a31893cbc04ba
nonce: c67aedc747e5b2d625a794f3
exporterSecret:
64e305afc56024d47175b0eb5ab58c9c67dfb1277649a8033aff43d13dd12665
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c67aedc747e5b2d625a794f3
ciphertext: f42d8712415002bfc6ef1b4e929d8f7a84f3e824e1e13a1ffb5eabfc337e
40741952d17aeaddf5c98eedd433d8

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c67aedc747e5b2d625a794f2
ciphertext: 28c7ad191f6ca7fe2c4e05d12d8be7e5b883e63f6d2529991c17179a62b5
9345f4d63a417a8ee000fa90aa3841

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c67aedc747e5b2d625a794f1
ciphertext: 98314d2da7ae00dc16e1751f35822152f2b7dca349b9391a523ad1d3bc74
acf79c32e71e6546d52d469ac49add

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c67aedc747e5b2d625a794f7
ciphertext: fe58f3cfd2b0ec6e16d578129673da93e95088b6e2273608d12fcf04db08
0fca2a0044fb5c94e2ea260772ef0b

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 3f5d7cc76ff0aaf0850df927a58c09a8ce709f7bd3170a3bcd2c7de00aa1c8d8
skS: d2f1e9d44ef674d89ff9ba128bf62d36b2b37e00b004c91bb9048047fdbfb780
skE: 813b4cdd989bb7801fd27a58efecd0f2a61f35fe4217b9718e957ce29e10d3ea
pkR: 27e63907816406206a56ca1a813ddab2d4be8e0a9b65f21ccc0b1ac33e16d71e
pkS: 59e95c871275a56ae8ed77deba58f9be47344ddc8785ab5fa9f1eaf68435ed77
pkE: c38bf2c95775867797a3b7fee4d77552065fd8b42e06c5debf2b96956db2470d
enc: c38bf2c95775867797a3b7fee4d77552065fd8b42e06c5debf2b96956db2470d
zz: 59061f4f9abc9bfb023f204bc0782c196086131bc1860af9e094018a24696598
context: 002000010003027c06ab49234d271ba849bf112283c4e965da8969454eebfc7
187029d62893ed59e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 3e1fd3801fa1e605f47e8661dbac24d7bfb1388b8b97c204b229cc4fcd2c5fe8
key: 8467ff7114f3baa4024b4380563f2ea37c23b39e0af0838268c5e5bd27bed656
nonce: abac6d6d1d5328899c3a35ee
exporterSecret:
7b2bf6c37cd95546c62336d426abd5c85b0939506efcb884ac21bce6f59fe024
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: abac6d6d1d5328899c3a35ee
ciphertext: 3637294e0aa49a0e2a9ab9280544a51731534180387d130e0eff35852483
6cc71fc1d085c86eb6265a98f48f01

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: abac6d6d1d5328899c3a35ef
ciphertext: 21de6b43023a6d9277b2d7a1a80f1364f84ec0d821910079fa2d72599825
aae0c6bb8f1dd9f648d7421e623cdc

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: abac6d6d1d5328899c3a35ec
ciphertext: f9e80ceaad38886975ab765a2add936a8542eaee27a5072ad2c59ba87f6d
3723de8742c18c895452172591999f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: abac6d6d1d5328899c3a35ea
ciphertext: e134a71da7f92852c17c74a814fa6694eb32fcc676d614e87d6735761e04
8cf71c0f5d2edfa6178152bc5a562d

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: fa3e9e95017c596e637e5fcb04fedcd00405ffa0052ceceff486685b8ccfeadc
skS: f9431872f1df5220655531fd7b732570293fee608df8de1f58feb9116bf8cb63
skE: 27c576f8cf45ba7253e528c12b1f8c4780b05c81cac739bb0654638b5f9f6f44
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 43be49c34807aa62ea7b1ab68eac20ec583b16cec95b67569e1bdaab93848972
pkS: 399eb5dbed9f174ffd002e2133478c7d2acf83a06feca8f547547295b61c9517
pkE: 7ac8e62fe5479f5d7f7517eb900a9788f549ae540d0d029f77bcdfd867e2b57a
enc: 7ac8e62fe5479f5d7f7517eb900a9788f549ae540d0d029f77bcdfd867e2b57a
zz: a54bc55bbca47e60e25de6fd1a5f28d6155102f0cfa5c22a0b867351121a5f9d
context: 002000010003031c417ad62e7adb08b7d000c720cff8fe718eca97fabf4237f
2779a2b6d013a389e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 0f28e47a3dd889249950c19e2f0342a2d07980d59b15bd565a339981cc5b18a2
key: 8035bedc25c019fe3d1ab781e8251cf1f74572b6880923bc2650cc15b1d1e60a
nonce: 9d68a2a79d908a8dc393b321
exporterSecret:
9991c69a40a17be5a501e5884c007d755bb226f475f269ac22ebbbcc5cfc840b
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 9d68a2a79d908a8dc393b321
ciphertext: 76aa99d5ef69b66cc56a9235314891da941bc01026b88a62340d587e76f0
0101788798b43b3d715e90d42e7614

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 9d68a2a79d908a8dc393b320
ciphertext: 57e6c7c696e49e1c9a79fdb417621bc94821762e3c75cb09d70392be00d8
df14dd60b7edf3060e3164bd0904e7

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 9d68a2a79d908a8dc393b323
ciphertext: 87b1db1021eb0cfcc2d55565781d132a9ee07adc7625f689fe4d317a2f2e
617ae84e819c15545b1cd729f8bfc4

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 9d68a2a79d908a8dc393b325
ciphertext: 5a4c736c975979732a48a7cb29fb109fb922bed44b1afba170abd1005233
525bda06e52adb666f5643415e81ab

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, AES-GCM-128

### Base Setup Information
~~~
mode: 0
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 1eda43a1669e0784454265d8833e716a5361c86328c2f732f2ea5ad07274dee5
skE: 0c4a146cb2fe7d9071a442c95e3c25abd836227510ece622c26530eec93afa1e
pkR: 04a2f57454b605b73101a23a80ae519306081435296c9489a9a06b95638cd413c91
9d60d7863b4018e29e238cc11fe8c4440a1476ff54d5c94f25c9c3b968c769e
pkE: 0422e9333cf6e9057e3f01447b31fa366d2fe74c08025d7d967bf8d0ac5b423f3b3
04ff75248961784a67e9dbfdd2c58d3c6bf232d1f6e6abb85b15ee8e27c9d81
enc: 0422e9333cf6e9057e3f01447b31fa366d2fe74c08025d7d967bf8d0ac5b423f3b3
04ff75248961784a67e9dbfdd2c58d3c6bf232d1f6e6abb85b15ee8e27c9d81
zz: 722a0def9ae99d5f395c589a595cf1a79c57f0141f2935a287a698967c886469
context: 001000010001007c06ab49234d271ba849bf112283c4e965da8969454eebfc7
187029d62893ed59e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 3917c6cdbe78d7c3f8af7d4cdce852c0abcd48daa8deb2aaefb8009c6e11edaf
key: c565032a7d4ec77170004664cbdf9293
nonce: b9ef59645b6119a4c8d12c6d
exporterSecret:
38a5240f4977ec1b79a05e704e9e68c6f6292f5ec241b0346f60486208dbbc15
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: b9ef59645b6119a4c8d12c6d
ciphertext: e8fc69bcb6a40f3c5b71de27004a1133e13f2860f5e30eb2207d96d86664
8cf917b04f2423cf8b2bfd1c0de8d7

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: b9ef59645b6119a4c8d12c6c
ciphertext: cdaf15968e7ba7c7c962ba053ab5e817a87a89890a104c00ba2a71c65e26
7c0a09bcfc8958ff5adbd0ff6fb043

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: b9ef59645b6119a4c8d12c6f
ciphertext: 97ebbe0900f95b97c3172a0be44c0af845050f6db712184549515017b120
e14923ede4a54a0759ea4a6d98a52e

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: b9ef59645b6119a4c8d12c69
ciphertext: 4c77fcc7e652140aed0dca4d0972a2482cb9e224bc703887764eb2b0da55
2dc88b0e8c2f423521558975463195

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: df3008879a2cfdcd12d5871d7ba51df22e4b67b4b8acab970111e748c3c074b6
skE: ab1057c778fb2887db6da2402b61ee418e7e2f196e2f9db5e301ed7e3c3fca53
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04cb6849344253a3f00d3afec99afdcfa89b1e750e57dec7f6e59cd0adf7d750049
1a60139c19acae1455588c5196266dbf7cb6fe2f38f6a1dfef720b7e4a44ec4
pkE: 04da687ee5f534f7b26b537f3d751e2e4122bb036ca4bdf0354661f0e9b0ccafd79
f67cae56995d78e1fb68d56566d9bec03e674f7affeca051fda5201f3edeec0
enc: 04da687ee5f534f7b26b537f3d751e2e4122bb036ca4bdf0354661f0e9b0ccafd79
f67cae56995d78e1fb68d56566d9bec03e674f7affeca051fda5201f3edeec0
zz: e36d2a1c63c2624fc995b3fa5e9bd5c1d0bd39e6ef33fab5ae7f4de4053c1072
context: 001000010001011c417ad62e7adb08b7d000c720cff8fe718eca97fabf4237f
2779a2b6d013a389e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 98433f27452d8ab5eaea9a62d065afaa68c5e42b9adcb3e659c679f16313c0b4
key: 137e37c54f7440fb0085d5d690adc5bd
nonce: 925f158fbf62feb3a08a5725
exporterSecret:
c08b47967b27d286f6456c121bcd34eae4bb3ef7cb8985148b5d9ab0686c5a1e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 925f158fbf62feb3a08a5725
ciphertext: 4d3e942045f276cbe5700fc1436d7b7ea1b48f37e81294620c979b452e57
26904c12c17f11d38066b922b070ae

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 925f158fbf62feb3a08a5724
ciphertext: 4b38ab132abfa6c8959667aa726fa9f62328e4af1efccc48224a67e75507
3638482ec2dae41662cd709dccff9e

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 925f158fbf62feb3a08a5727
ciphertext: faa6169bc8a2c85b71afaba9d5360ba8b81bdea4aa49c224725961f35121
68f7f4a12efa010411d1fc6872906a

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 925f158fbf62feb3a08a5721
ciphertext: 2c93b6de373d9c5afada0cf7bbb0be8bc95f2bcce137bfaf03398e6733ff
0ee7f9ed66990ef71747dabb7aa717

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 84d1f996df52b9dd55c91d0bc4ecc4799d3ec6921c22dae9e53a75f3e7ceb49d
skS: 38f5a7082a8b8bb581b4ed95c9c5ba14942c01cac187b26d7df0bbca77cde8c6
skE: 6b766d955b19a713f54f2cc4805015f64f659abdb0296ee0468e14f864e713c3
pkR: 045e9b59f3f31d4b56169569599300b718720f8e7bf3cb57efef683dc204ce13c63
33914f52e8cf40f96893328987d4b6da86c25a73843e6124ae00f9855f451f1
pkS: 0432b5629b9bceef6de778290d7056e7f3ad1e456cf832bc0773f57861ca095d992
5d1d1c563c2a3358166135f2d7b9014385a2ff83c8e12991144ba648ca4a8ca
pkE: 0430a797ebff671c28d80b15a7023922504b56027b07b63d5b2bcf47db674887ece
8a788695541ff70df71cb8e34297ebb97b2e4f2d5a54bb2c6ab5c6481d34ea7
enc: 0430a797ebff671c28d80b15a7023922504b56027b07b63d5b2bcf47db674887ece
8a788695541ff70df71cb8e34297ebb97b2e4f2d5a54bb2c6ab5c6481d34ea7
zz: eebeb50db5bbd2a3eb2241547e7fb80cb40f2b5110838f981627f2ccc5b8ed27
context: 001000010001027c06ab49234d271ba849bf112283c4e965da8969454eebfc7
187029d62893ed59e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 6f247210e4fac016c6d4f0c1a8f2444c7e003a2099781d1ad56b0122b19bba67
key: d4a02d8be38f89dc68d2adbdf08e38f1
nonce: 4db49246ba8f980d879ba729
exporterSecret:
870ae29d626f348efcef637f1f06eb4186851e3dd17079553665e2869a7bf110
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 4db49246ba8f980d879ba729
ciphertext: f512fa0fb8e01cee304b663ccb89b871eacc80fe765b24054aae69c6a79b
7ad0219346dc5b141d014680c50253

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 4db49246ba8f980d879ba728
ciphertext: fa25c3616f75b8588a9c0ebff789ad99409e03bcd748de5e1895e97504e7
c971055d00fbcf435a4ea01bc15498

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 4db49246ba8f980d879ba72b
ciphertext: 57dd84453dbb3ab1976dd71142c104a4fc1b8f624557b9a8ee13cee5469e
85b4858b66b2d345bc1d3f36e06ab2

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 4db49246ba8f980d879ba72d
ciphertext: 717ec6d45d0017d107853a32acaa929e6821cd4e66a6e79d2c9e386c93f3
53542e57e579592501fe069043177c

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 8fc69d3083edac9b00853f4edb6f2979860e65c556d2a55d99ece570ef1502e4
skS: 2175d38e30cb1d14f01622a617db21adc16344de82fe85feafcabdd60da4ccd1
skE: 456e64b91c7691930b8edff2037573220cd25dc87f9ee6693f7f8115af3a12c7
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 044bdda0d990b0dafde590b08013e089154857c637a26d5ff411d5d530d30d046a1
b76a62096c9b13336528c40cdc4d0075202bb3d8e39a0772c26c8d3cd7f4095
pkS: 04869487901ae8d607c4ad2a35904e4881cc807fbaadc4dbf5b42a0ec4c6dd02a85
39c1ce3fb83feb5e96d996e1f3be58f8051c383aa00d067a5a449d11a6c672e
pkE: 04bff04e76f759319554a7008232d027d6e518d786bab83b453e7c22ac0c527c2f4
ecc6283bd8afa2e3a1cbe2b72d01a5928dd90174136ae6d0da40a6f64a841a4
enc: 04bff04e76f759319554a7008232d027d6e518d786bab83b453e7c22ac0c527c2f4
ecc6283bd8afa2e3a1cbe2b72d01a5928dd90174136ae6d0da40a6f64a841a4
zz: 6c93f77d8985fe76218b84deed673b3d0b41b00d5633225ed94ab8da600ecb7b
context: 001000010001031c417ad62e7adb08b7d000c720cff8fe718eca97fabf4237f
2779a2b6d013a389e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 4047a0f800097b0ef01a781411b34432f567bfd26c10efccda4d3758d799eb2a
key: 17c6b6c0d241827575d6c10c1fa2d9c1
nonce: 72803f50f1d36f8ac4b6894b
exporterSecret:
c7f4dbc59a3fc512c026c204ce18d0fdad8fe8b7b4967ba422728e88a0e1c541
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 72803f50f1d36f8ac4b6894b
ciphertext: cec1365935e5e9b288f0ef3dff6e872d3d7b9e5d41122610a25d745fef3b
8242db42cb7e8a155178f7b935c6e8

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 72803f50f1d36f8ac4b6894a
ciphertext: ffabf47df51d781d0e4485ec4d086f2ea2f5f3298147eb118ae678a35061
792060fb6246bbda7b7678a6feb060

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 72803f50f1d36f8ac4b68949
ciphertext: 8bf4f08283e4ac9c055dfeabbdbffa8ee0d2be464b9fd05bf155b8c4194e
73027f1405733fa83eb81f4a4ada60

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 72803f50f1d36f8ac4b6894f
ciphertext: 8be76f80a1c22610ae6b20202b61b3da3531a592e2e89b509417a9a0c9b5
94e73197085318168c8a6250b2d370

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: ecd274607e00e118ddf49e4414ac6841c40427152689e2dcf3c2e8b2e3db152a
skE: 46e819e1a0d8febb6a0cf9dce5bb5b485b14167355823c2b378a746722458234
pkR: 0410b8cecf426732e5d712bcb61f8539e223501f0097734c730c96e416f71cb359f
4058de9c82a1dfeee566b42e059cff5f5d68eba980a236e4881a7db72b91331
pkE: 04ce4529b8d14db501b7c9f08894a38510fbbb1ad19eda07faf8cb0f3cf7ba7d59f
c6ab3944bf770c5f48a4318c87addbe9780aa1dcd2b0f9772366594b455162c
enc: 04ce4529b8d14db501b7c9f08894a38510fbbb1ad19eda07faf8cb0f3cf7ba7d59f
c6ab3944bf770c5f48a4318c87addbe9780aa1dcd2b0f9772366594b455162c
zz: 033f49a3e79c0a0ea8168b42451a24eeaee111857c081425db3ce0c504ce00c8
context: 001000010003007c06ab49234d271ba849bf112283c4e965da8969454eebfc7
187029d62893ed59e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 8a9dcd78df2874775ba4596d0d0923a8a73d2e0f98157fbb65a041848251d145
key: d7406c56899fb9ba9a0fc3c93d4f850ea9f85ebcbdaa941f6811a3c4cadd15a3
nonce: 2945add4c75e59cb4edf7bec
exporterSecret:
d4ad921055b32a07f0554c08c1bd8d6e501df4882b57d31080b1766f803e7a1e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 2945add4c75e59cb4edf7bec
ciphertext: 30fec2601aa58a37e2c1896feed4109eddbfe733ed9bd2f2480fe7ce2531
1f845d976386e758d69bfb6bef082e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 2945add4c75e59cb4edf7bed
ciphertext: fc6b031cbe3b8f5be56c527ab2f15dd7d2348e9f958d56bfa4878590bf83
20f3cf3826f04e22826ba0c5088240

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 2945add4c75e59cb4edf7bee
ciphertext: 7b73cd00415f7fb9a3ba1288ac69af0436994c3e484311a6f196e357edb4
cdc85436bf8cb5652ddc3d97e390aa

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 2945add4c75e59cb4edf7be8
ciphertext: 1965fa08b7bda16d57366d6b64063795fc8271d06ed363d57003e4f04ec5
9680e620642a01df92b6b1524aa612

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: f24f21e9d02a24e6d70e35a3cb40a62ae1080390bafe9f08503a729c436754ff
skE: c27f0185d5eb8d808da8eaf988b7da39aae27ff7b9fcfaa044306ade80d6da57
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 043eff5330051ad852a1e4f2e3ad69823e203853ce642508632434262b2ce4bca7a
e2c0a72c125f231443c35d3a7e0217b0e3183a21a3cfff7a276dea6afb5690f
pkE: 04633051efae771471d19ceb7221cff8afba5f5cd0c75d072ef07819562a70dbed5
05f84f506b54e0be26d135e565ac1ca0dc5e80bf98e172692be983c36887b68
enc: 04633051efae771471d19ceb7221cff8afba5f5cd0c75d072ef07819562a70dbed5
05f84f506b54e0be26d135e565ac1ca0dc5e80bf98e172692be983c36887b68
zz: f87ada13b8feb0bb8bd3671455dc34614ff2d14d8f1c60cbe378310c08a0d93b
context: 001000010003011c417ad62e7adb08b7d000c720cff8fe718eca97fabf4237f
2779a2b6d013a389e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: 0cb96a02dc7a741191ac081f42b7cee1d09570c7801e9ed789a7e993557d4292
key: ddca8ce0dc6dd405eba2f0a6d45198d5675feab29cce8d20fd4594b4489962f3
nonce: 4dcd0083550b37b4c5d7615b
exporterSecret:
d2c08a6a6afeaafabb7d4a67cd0db00775c9d1416ab54b9791e12ad43b0731f5
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 4dcd0083550b37b4c5d7615b
ciphertext: 99113c9e01e458a913126f4dfcdc5036e8f201672ac65e558f5b91f24622
5ae55fa272d9eccc1fc7d47f959f4d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 4dcd0083550b37b4c5d7615a
ciphertext: 0fb6d63fc36c98e88abbd76a449b293d0756d09adffb0d2fd33702b99c8b
813aa19202f8fab09cd8298a11817c

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 4dcd0083550b37b4c5d76159
ciphertext: a62841994af5cc58bb30614df85b590deb1dc4eb7478596b8f0a1074e723
8c03be5e612997ea135bc81d3ad798

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 4dcd0083550b37b4c5d7615f
ciphertext: af291ecb6bb915f51de396fef0aa5b614a2f82494fba79a963bf7e67acc4
3387c526be8246ff27ac26fe0e9f12

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 2480bb5e302fc6369f4c788760e51a0487516ab30a365c61186d62948706a48c
skS: 974fb70e0b316c236aee51947df612f5d37ad64a4472cd7fb947e29e971f0d3a
skE: 91930422e0298be8a1369dfb1c11a5f5305f513d797bd8e6175f23fa8b745e96
pkR: 0412aea9f5718179baeca51c31943241edec9a8c4d0656c1968e47b11ec90f07cde
4a00a4d90c4740c0b5dcab67949e25f4d4252a700a39082e88409f8fbf76ac0
pkS: 04c3a1ede586733d9f2814b96dc7aaebcdaad105df593032105ddb5df772046dc86
3cd3576e0c4942b9300c3af6cdfa76e43eaa525cd7ca73130e0706acdbdc0e8
pkE: 04c9e6efad4ab6b12a4fe394c4c29f46049fcd0de846fcb040eed801d61670aae40
32ba271c689c28029ff933800de49fae20f0dbc97556221c3ea198c1eafc367
enc: 04c9e6efad4ab6b12a4fe394c4c29f46049fcd0de846fcb040eed801d61670aae40
32ba271c689c28029ff933800de49fae20f0dbc97556221c3ea198c1eafc367
zz: 8364ffc2d7c467f35b272ffccf8c4d1e4ca638192ae4093e4a243f872de87915
context: 001000010003027c06ab49234d271ba849bf112283c4e965da8969454eebfc7
187029d62893ed59e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: ea55e57f35f4b6ada77a45eb4a29059d9838c48055bdb4ea7a2213239d7e06cb
key: 2dbcba5ce45dd5dbe4befb741d86aedba34656af9cd4633580ca10e25b70d93b
nonce: 80ee843598aa8a75e6bd3b7d
exporterSecret:
1bb0504df0320aa9b1443bc12df1d4c1ed3e1dd4e7212c069cdff3e7ca550ad7
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 80ee843598aa8a75e6bd3b7d
ciphertext: 422fb5e888bcf0675d7eeee2f82aa83b2593dd2bb4d35b442c9d54cf8947
8962f5637cfdf602c298285be72eb3

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 80ee843598aa8a75e6bd3b7c
ciphertext: 8487324718372339baa2b81c763c7c50c81e965169ee57aba337f6aeb925
2f5efe02d811b275ddcbfcf1d2ad6a

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 80ee843598aa8a75e6bd3b7f
ciphertext: 60e841beda4612951ce46e09f9f00576624cf4e0eeb381cf07ac141315cd
6f6e4cfef9dd89cf79c450461b214e

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 80ee843598aa8a75e6bd3b79
ciphertext: 4556866964b08f5a00596b853f096aab612ee38032e1a2533eae9068d5c8
d7cd29f753984e0738ee7c0d743363

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: d9236b19f4fbf36b05a43a5c028d9dc5e794f6719e63f531c2a516163288d81c
skS: e811829d25e7a6c224e2680a05e4737c80007e62a823090e4fc70343788d45d9
skE: 95eafa0d92a09d03650efb0b5b5cb0cc47e822981a158c225bc9e00697f2439a
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04d0bc6e3f041a29d5337176e464676fc742c91269fef85e0950ad0cf9f4df992fc
b88a59fab4565ae636347016cfb9b416b95fa498f970d79ccb275c3363c05e5
pkS: 047b870f7929747f6870bb6d5fd06aab30b2ad6be3198b0df3856058dc79246d126
98ce340507aaa680014ac5e6344504a80f64e161e8d8c60714f8e7c854e12f5
pkE: 04ca2efe1d0add050181f1500237fa4065437d27b3f3131cbf1664f39eff9c0b839
e57736a7a353c492d94ab507e2915bd6382de8f2cb375335116471a33203f5f
enc: 04ca2efe1d0add050181f1500237fa4065437d27b3f3131cbf1664f39eff9c0b839
e57736a7a353c492d94ab507e2915bd6382de8f2cb375335116471a33203f5f
zz: 8be21282d2a9227a549f108d888bcd383156404b72148f02c41f400470e21161
context: 001000010003031c417ad62e7adb08b7d000c720cff8fe718eca97fabf4237f
2779a2b6d013a389e3cec2bd4e7128a963d96f013c353992d27115c0a2ab771af17d02c2
528ef3c
secret: fc7d70ee26c4009d01fdcb0360ffe1e542edb4562a1885187790d6d199bc0574
key: 0dbc81f7514ef5181d212be5ed7985a22ea26598af6ad2158ccc4210dd86c1e6
nonce: b2c29d371adfaa7eda7c5876
exporterSecret:
5cde00651dc1fa4a48986a3016b837ff9ec9033cef8797adc6b41c3e8c0cbb74
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: b2c29d371adfaa7eda7c5876
ciphertext: 4a2d191576a6ffabcae8a69cb59c921dc0b4d2c025851146a3eee32384b9
085c7c0c659ee0b266ea9f4ce9f9b4

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: b2c29d371adfaa7eda7c5877
ciphertext: d9f9899b2d841acdfe4378524ac718a660d8798eb13622001871475203c4
c2e728ce23491e33057613fecb3832

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: b2c29d371adfaa7eda7c5874
ciphertext: 8a981592c06556db73d73004e4c7f63c42755d5bc67a9cdc2c91fa9ec945
c43cb798a4809657ad8fdb334fb1ca

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: b2c29d371adfaa7eda7c5872
ciphertext: 8997eb03746bcab884d612c8638d3bec88f2400b364ad9b0ae73afbeca27
aa92c0c133572e7f384ea6cc15bac6

~~~

## DHKEM(P-521, HKDF-SHA512), HKDF-SHA512, AES-GCM-256

### Base Setup Information
~~~
mode: 0
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 01439154b0bcc96b69d0530ac798f6ef0dbc35d635397a02a01da61a38ffab2481d
900c2896e7b0a264b475151439cc94920f5d82ba52b75862ecd6ebe69d084c702
skE: 0122bf65e3d96c7a0fea4d7f4aa7deb1df009d02d7ae38ec4d12fd8952c70dda902
d6ec52c291b3c9cec03cb384ec6ccb8a878dfe5551f2685b8ee7e3aa59c628109
pkR: 0401e0d89e7f9090780fa9574dba97da56c500fb10a740d1d7b68672aa80b1cb705
244dd097d573703a1df0979c4cbfda6637fd4cbd872c62d8cb548b7c389e9ccebd200937
f24c259748ff05180f4b89a473a3f2f369fc5b510c61f6a993b626b3aaa04f06bc03da23
dadfd00d4f857bc4f6c8a358d3cd75001fc5651a79e300c60e58fa0
pkE: 0401cbcda28e303426671efd9c7048a4adab4f3ee2d39eef55fd6fdb231a2a90281
fbcab2044a823e0be66dfc54547b21fac76988f9768becb148c287857610370d5cf00b17
59974ff59def6177ea3013a3a2c73c7523efde4f85ac9e0793e5a58fd2051851fc390f71
a8598e916720fce6a40e938422fc024ecb3ffea1f35184179fdfd4d
enc: 0401cbcda28e303426671efd9c7048a4adab4f3ee2d39eef55fd6fdb231a2a90281
fbcab2044a823e0be66dfc54547b21fac76988f9768becb148c287857610370d5cf00b17
59974ff59def6177ea3013a3a2c73c7523efde4f85ac9e0793e5a58fd2051851fc390f71
a8598e916720fce6a40e938422fc024ecb3ffea1f35184179fdfd4d
zz: b93288ea81ca32d0736fcc4786763dc8b3098d0bdf4bb94da9f5ad781ba835383ec1
faf48b17cc920311624b50bde320a447a26a72499703990c815fd6fe9f37032b
context: 00120003000200da5b7813522e89c89132c72fd04de1dfe81a510b506aa2754
6cf58a91b915d45beb646b4588c1b5d2779613b5e0ae1ae800924c0dd923df2102859edf
41c882fa4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: 14d74263c01d7d49aac9f2ad4f24dd44db00dc52dac655d4b4340786033b19e4
bfd913aec9a7871775e449bb98a79abd94d74460e87cb4d7dcfd6865db8b0903
key: 5277d1240ce311ff88ad5eb578fd7590bd3a1e6c837849e3f2342c5b87c3f307
nonce: 10206a3cc413df8d23a043d8
exporterSecret: 839d2c13a4a5904faa66b2b9c5e527e73efbf48c2ac1c39295984a89
beaaa4120f1e85b5622354b99a3369ff7b5664f541c06274e9465045b1bcec3e8ff53a6d
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 10206a3cc413df8d23a043d8
ciphertext: ae722289faa7663456f516b73a406331b0bdc656906f8997244f4b3defed
76060deedc7adfaedaa5b9469ba11d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 10206a3cc413df8d23a043d9
ciphertext: 8d010fdde038e8aa6552f2079f781ee100f47e51118f63dcb22cc9ad54ab
37fb10b5158bccfafe8f64e8b4a58b

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 10206a3cc413df8d23a043da
ciphertext: 7ae6062a07a56bae062ed314df8f91e70926d8d3cb03d3ede6b9195f1a0f
09535c39f33a756eab9c4e725fac58

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 10206a3cc413df8d23a043dc
ciphertext: f72514f313a2d654f772fe19b028bda38cc94d02c0efe1b698f65e305505
b7199ae363882ede9291c0fd98d405

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 01e0fa2824167eed9e99ffad457a990cd03de4439fb6a3aed8e9c5361f88b2f468b
14189340cf833f60bce21f4b95243978cd34099e8547f0c62d4a0267d4ab4e182
skE: 0095d63cce33d3868d6cf3a1ab9b12889936ecdcb15ca54aa7ca37a7131daebde28
86603fca0fd945decc0c12169cffd6175117043e41991b25452834f18a248451c
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0400fa3918b0e2049f1f58887a4c4010ffad6899c20fc5efafebf648e18d83ebf21
bacbe817d457f9926f4c33aee4ffd6ba0763746196bf62625325d6c60256d3cb6d101917
0cbd7808a1206241e7362eb704c26802a2ad05f757d7e72d5b2f1e553b1d0055f9ea06ba
1171ebfc32582395bc9071725f5a5806b2456e9f3fda55dfa5568c9
pkE: 0400d48fe7c73696026b1a500ce7f87588895a8abb97dec712333ad8d3ca2b2654e
7b9faaefc0424e3ddd8b973871373dc875f4728f33d3ef21ad17fd1ae0a82bca27d0139e
b4fded2e640e5bcf423e397f1653c352a57a60cfadb964c7a6502a52040fdbceca8e8f2a
49587d5b94163a73a2f0d27a78fd469c3ba4efc8cbcdb3863e2bb00
enc: 0400d48fe7c73696026b1a500ce7f87588895a8abb97dec712333ad8d3ca2b2654e
7b9faaefc0424e3ddd8b973871373dc875f4728f33d3ef21ad17fd1ae0a82bca27d0139e
b4fded2e640e5bcf423e397f1653c352a57a60cfadb964c7a6502a52040fdbceca8e8f2a
49587d5b94163a73a2f0d27a78fd469c3ba4efc8cbcdb3863e2bb00
zz: 6d76d95563b2f10c9cb388e1e336b306f98ac5de128c392f24cadcc32e50e65771a8
a14fd5e93112d44c327409cd6dfb41e8bb65916d74bead42a87add05a4e559af
context: 001200030002011cd2b8432f29072053d5610e170618bb69438f9eef01ff985
60ab714a02832b43c773339376d370e801c3786c183345fd65846d3946517a8966050c48
1414ed3a4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: 3d20317944dfecdd43164838ba2a00c7fc73d7decaeaf25ff9d7c21cb0b11972
b241ca40e0b67d25d87f83fc2ad2bf26e66fec17f4859e1d17c6077d8a2493a5
key: 1424f34694b36c689aa1e669b23be2432f76b648b6655559b83e17675898a6e4
nonce: 58eb621e04482cd253c09a3c
exporterSecret: 1495aa6169625cc8ba1bd3f84ed8cd23d851655e18ee21fab48b74c9
ebb9689c2c1487a802d1dea18b75a9a6bd3c6b1878fda4e9ed581a00324626ccb528aee8
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 58eb621e04482cd253c09a3c
ciphertext: 8a8979fa2e1255c11a5f0dfbde2e699447c7a6a397b0562c9fed4109c816
14e0d066e9f49b7ae42377b03b1fad

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 58eb621e04482cd253c09a3d
ciphertext: d4e1daf4871b5cb0f22dc77585b337b9a61989abd62b96c076eb8950cd76
5c7e21422c4669ffac0e5d69a3017c

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 58eb621e04482cd253c09a3e
ciphertext: a620da7ff4191f5610f2da5aa497827fa600c20b0ebc100f7d4cedb94fb6
8e44b8cc42a9204a9ddad7125eb05b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 58eb621e04482cd253c09a38
ciphertext: 7d65021e0b0aaecb2645abb9d82a7cd93669875877771dd025b9e3498146
c2c47a347e67ac5593c373d59ad968

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 01cd723a0d9f3497fdddb26eade18a1dce7c7d08d09cfc19322df68bfd6216568a4
2e3149742b71f870565e3d70310e3519c2bbdb5abdfc726000ccd86af49a79834
skS: 008db732fc84b0c0e149a53d275c8d1b2bc679007cf6c7bffb9daac8918aae7e253
3d551d832e5baf2c3635648bacd9f2f48e8b64f28e20f16009e28003c85e26bae
skE: 00665f10a35a1b517605ae0f4a020b8d598ffa6deb0e04670f703f6e93f98e41739
a4f911da2c16bc02113d6c205f6dc86380c6adbc500929e4f9a7e8b1f3b747a47
pkR: 04004a6814f279b1f4c81c5e30a0df2fecca1ffeed3ef46582abfef2b7a7dc7741f
c6e0bd7b94972a33e3d36b56487b8c595b011f2af5ed558f08da92a9545634dfc8801f30
e2bd21dd993b9488d9b49b04a349a3da6ce470c195e26eee960e4a823a18350182025d3b
aa6d332773628b0e371a18c5e37d3a0e31c47bdaa4817f8cd4704c6
pkS: 040085672e9459a2b8ac00a0d69789ec5475c8f323e7a8a0562b1e63ecc4b42697c
5881bb8a4c969645e8dfb42adaee777c3921e9cc0004934547a87d50fd166c566aa006cb
eadc909bf7e020078e675ede56f2707cd34eca0cc94fb797f4c4aafd148efd7e3c25a5c0
73bb2705c5f93a8f25cb6e25b4d640e24b2be4b6bd55d86a11e82d2
pkE: 04011ebf592b281321f4524a62f56a73e968bf058436a88116b525ab1fababfcd95
254046d4de6e9b6ebf405655da166ee28eaa7d7b12d99b3a049f04867fbb3d875a201210
d8bb310b5e0e930773c4e19f94af4cdc911f9861714c9c776c13ae9959ad573d4eac613c
f481cfa22ff2257f9c403cf31c5c72d581c601d1af442b398850438
enc: 04011ebf592b281321f4524a62f56a73e968bf058436a88116b525ab1fababfcd95
254046d4de6e9b6ebf405655da166ee28eaa7d7b12d99b3a049f04867fbb3d875a201210
d8bb310b5e0e930773c4e19f94af4cdc911f9861714c9c776c13ae9959ad573d4eac613c
f481cfa22ff2257f9c403cf31c5c72d581c601d1af442b398850438
zz: 9b0668b635b66b29fafbd20073a99659d15c8d3ab62f1c093d59ee1f260085ca815d
c6abb5723e1b112ed0540dd9d34713516610aa2ab71ff6cc8fcfea6921ffaa87
context: 00120003000202da5b7813522e89c89132c72fd04de1dfe81a510b506aa2754
6cf58a91b915d45beb646b4588c1b5d2779613b5e0ae1ae800924c0dd923df2102859edf
41c882fa4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: 0886ab976ee6324cd806498459e63105d91838d678ce614cc32de9324c528c64
1e4a0a3359f6999d329638c6a3f77d095b486ec6cd4fa64da2d2e1f84b69aece
key: 890072950c2cb38175206456396e9de007b558617898e1017817a9baaa43abea
nonce: 08a54c31621c3bd490335d60
exporterSecret: 3066c90780cc46765f92bf4dd4660d327eaf18116cdc0c6af5db5635
06a54281f18cb6ee54204cd2ffc8bf4e60ecc0f096348d5f4bdb64e35905151462b1f1a1
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 08a54c31621c3bd490335d60
ciphertext: 2514112656e102756537eea63eee1af3dde2daa69e8041ff9b4bd19425a9
2ecd2c515c9533bf42d69e0d3c87d8

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 08a54c31621c3bd490335d61
ciphertext: 51101b5b84e9b8ac9850fcd535ea7e9d5d700abaee6360a388629b23eb1c
46b40def4fbde4c64599d64e27a400

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 08a54c31621c3bd490335d62
ciphertext: 7da16fe3574f66bfe7413949acd273226fe268e69363ec5672df230ab1c2
d3257f16b6edb5e003afd6f6975c1d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 08a54c31621c3bd490335d64
ciphertext: 772b0557154030491d6a15a16d02aa9ab4fb2ea37bb12a52e12e59619e79
0d96e2f42cee6d281d34a20fad5215

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 01901f413bdaa6794b79dcd95740e87b7430be41ba24ac70778b48ba3db25b46db3
dd8630f5d1547700a2504314584e4023c1b397273dca4c267f8b786e19365bef7
skS: 0053c54de44fdd82b52dd4fd7003fdf25102122ee889504828348468eccdde8c92d
8e3c5d837d367851164fdbd2a873ecc94524be91c275a30924ca46f068f89266b
skE: 013e2f72a73bf3c7355fed0872ed3214807e88d3c3042097895cac50e756b22880c
fdc7c1424a1cc709a258e01a58b39e59d592465dae67741781e47c1a1ba1b9a1f
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 040024dede78461997bb0745087953897ec87da108fa6d744c908f91178f904196b
69db80a02963c765ae71379f62bb3a53c21a4717b9beb50180c15b3f48676f81fcd0054f
7055259ada18c0217e4fda0e54f28ee3b4f3bdffd9b205005f39eeef854dd8bd41a62931
0fa3ad77b5768ca8e7a54be08dec1be64278537ba06477f35ed69a0
pkS: 0400ad482c58ce5f9a42d429d28659d557eaf3c5b77fc123f3ce47115a0d624f67f
f730e4fd5c0dbea8ae1e4cbe539961a3dd71ee342b3c7922fec0a2a0c2deb1bb86a00387
052404f05fded22b365f8089549789cc111117b13641eb0db29e707a009322eae8cd4982
bdd7c31350a49b74edfdd04889de394aeaf901f8896715d066a4d3b
pkE: 04014b28b12ffda970685f9a09b2da0b668decd69d9e6cbdb41ef82ee6758d925cf
dd623af0cfd5f59876663928b16ed89110b70281afba5d82ee87884951b3b52d7f60108a
ed8fb259c95ff5cca60e95e3f523a3fbe85c8a831f71f9f31c2f8c077ae5b461069313fc
7cf356897b17d660e6d99b2897b3ac0657ea4afc3968507fa7c7ca7
enc: 04014b28b12ffda970685f9a09b2da0b668decd69d9e6cbdb41ef82ee6758d925cf
dd623af0cfd5f59876663928b16ed89110b70281afba5d82ee87884951b3b52d7f60108a
ed8fb259c95ff5cca60e95e3f523a3fbe85c8a831f71f9f31c2f8c077ae5b461069313fc
7cf356897b17d660e6d99b2897b3ac0657ea4afc3968507fa7c7ca7
zz: 6ec04a22f5222d359be086f1f2b6b864d28d3a35f0c1f9d5715dee990e7c5b671e1e
fdc2957e6d89e3a9753f4de0e731f1506bd8f1cad4af4021f6e4d09d25a21e1b
context: 001200030002031cd2b8432f29072053d5610e170618bb69438f9eef01ff985
60ab714a02832b43c773339376d370e801c3786c183345fd65846d3946517a8966050c48
1414ed3a4f3eeee6a7c7854f42e3cd9a44e51d2e6319ad0961f0684a97858591766f738c
aa06d9cc4ccbb55bec142df86258987e10dd94cb8ccb5fdf6dad38b3cb08124
secret: 13e284fde5aedaee760a8cae3eefc1614bf28eed4a65f6de7f9ed28562cab8c2
d0261452dd976df8b95a97c13f8decb2a488899e8d378b191ec23c866403c067
key: 09a86f9285a2ba8ae74124d07ea951d53c90dc6bb709b54d891bd516438ad158
nonce: d68a1acf7b8bb458cab4527f
exporterSecret: 2ca1ac8aa260da259b88b5f871df330d99a66ce3c237b4ce8b3a488b
f038bf63b351fa74e71e6d61a0072cd3989a3f7915688f3b7188fd9b6dd508880600b42f
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: d68a1acf7b8bb458cab4527f
ciphertext: a6db3b4602035035f1137427fce677cd75c4a3ded7dc8871d0dd07f0fe3b
8712c71693d81a482dbc9023949335

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: d68a1acf7b8bb458cab4527e
ciphertext: cca2284cd0297db48aafbe6aabbfee09f99f8aa078c3e1583413febecbfc
eb6ba2c17448c779c4042e0fa4be81

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: d68a1acf7b8bb458cab4527d
ciphertext: af957af762ff22c94eb2139180875356eb562e62c9a61b52e666f0c87082
c12b21266d6a9ba94a0119389e6fbf

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: d68a1acf7b8bb458cab4527b
ciphertext: 436a379f7d3566a6c87e06a51bfad65ebc1afae48c67f3cb07658ccfe970
092dff176628ba095d9b8e25dfb3e6

~~~
