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
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/1e98830311b27f9af00787c16e2c5ac43abeadfb/test-vectors.json
    date: 2019

  keyagreement: DOI.10.6028/NIST.SP.800-56Ar3

  NISTCurves: DOI.10.6028/NIST.FIPS.186-4

  GCM: DOI.10.6028/NIST.SP.800-38D

  fiveG:
    title: Security architecture and procedures for 5G System
    target: https://portal.3gpp.org/desktopmodules/Specifications/SpecificationDetails.aspx?specificationId=3169
    date: 2019

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
- `len(x)`: The length of the byte string `x`, expressed as a
  two-byte unsigned integer in network (big-endian) byte order
- `encode_big_endian(x, n)`: An byte string encoding the integer
  value `x` as an n-byte big-endian value
- `concat(x0, ..., xN)`: Concatenation of byte strings.
  `concat(0x01, 0x0203, 0x040506) = 0x010203040506`
- `zero(n)`: An all-zero byte string of length `n`. `zero(4) =
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
  - Extract(salt, IKM): Extract a pseudorandom key of fixed length
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

def Decap(enc, skR, pkR):
  pkE = Unmarshal(enc)
  dh = DH(skR, pkE)

  pkRm = Marshal(pkR)
  kemContext = concat(enc, pkRm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz, enc

def AuthEncap(pkR, skS, pkS):
  skE, pkE = GenerateKeyPair()
  dh = concat(DH(skE, pkR), DH(skS, pkR))
  enc = Marshal(pkE)

  pkRm = Marshal(pkR)
  pkSm = Marshal(pkS)
  kemContext = concat(enc, pkRm, pkSm)

  zz = ExtractAndExpand(dh, kemContext)
  return zz, enc

def AuthDecap(enc, skR, pkR, pkS):
  pkE = Unmarshal(enc)
  dh = concat(DH(skR, pkE), DH(skR, pkS))

  pkRm = Marshal(pkR)
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

* `pkR` - The recipient's public key
* `zz` - A shared secret generated via the KEM for this transaction
* `enc` - An encapsulated key produced by the KEM for the recipient
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

def KeySchedule(mode, pkR, zz, enc, info, psk, pskID, pkSm):
  VerifyMode(mode, psk, pskID, pkSm)

  pkRm = Marshal(pkR)
  ciphersuite = concat(encode_big_endian(kem_id, 2),
                       encode_big_endian(kdf_id, 2),
                       encode_big_endian(aead_id, 2))
  pskID_hash = LabeledExtract(zero(Nh), "pskID", pskID)
  info_hash = LabeledExtract(zero(Nh), "info", info)
  context = concat(ciphersuite, mode, enc, pkRm,
                   pkSm, pskID_hash, info_hash)

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
    // Mode and algorithms
    uint16 kem_id;
    uint16 kdf_id;
    uint16 aead_id;
    uint8 mode;

    // Public inputs to this key exchange
    opaque enc[Nenc];
    opaque pkR[Npk];
    opaque pkS[Npk];

    // Cryptographic hash of application-supplied pskID
    opaque pskID_hash[Nh];

    // Cryptographic hash of application-supplied info
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
  return enc, KeySchedule(mode_base, pkR, zz, enc, info,
                          default_psk, default_pskID, default_pkSm)

def SetupBaseR(enc, skR, info):
  zz = Decap(enc, skR)
  return KeySchedule(mode_base, pk(skR), zz, enc, info,
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
  return enc, KeySchedule(mode_psk, pkR, zz, enc, info,
                          psk, pskID, default_pkSm)

def SetupPSKR(enc, skR, info, psk, pskID):
  zz = Decap(enc, skR)
  return KeySchedule(mode_psk, pk(skR), zz, enc, info,
                     psk, pskID, default_pkSm)
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
  pkSm = Marshal(pk(skS))
  return enc, KeySchedule(mode_auth, pkR, zz, enc, info,
                          default_psk, default_pskID, pkSm)

def SetupAuthR(enc, skR, info, pkS):
  zz = AuthDecap(enc, skR, pkS)
  pkSm = Marshal(pkS)
  return KeySchedule(mode_auth, pk(skR), zz, enc, info,
                     default_psk, default_pskID, pkSm)
~~~~~

### Authentication using both a PSK and an Asymmetric Key {#mode-auth-psk}

This mode is a straightforward combination of the PSK and
authenticated modes.  The PSK is passed through to the key schedule
as in the former, and as in the latter, we use the authenticated KEM
variants.

~~~~~
def SetupAuthPSKS(pkR, info, psk, pskID, skS):
  zz, enc = AuthEncap(pkR, skS)
  pkSm = Marshal(pk(skS))
  return enc, KeySchedule(mode_auth_psk, pkR, zz, enc, info,
                          psk, pskID, pkSm)

def SetupAuthPSKR(enc, skR, info, psk, pskID, pkS):
  zz = AuthDecap(enc, skR, pkS)
  pkSm = Marshal(pkS)
  return KeySchedule(mode_auth_psk, pk(skR), zz, enc, info,
                     psk, pskID, pkSm)
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
  encSeq = encode_big_endian(seq, len(self.nonce))
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
Validation of the computed shared secret is not necessary.

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

## Choosing a KDF When Combining With a KEM {#kdf-choice}

The choice of the KDF for the remainder of HPKE should be made based on
the security level provided by the KEM and, if applicable, by the PSK.
The KDF SHOULD have at least have the security level of the KEM and
SHOULD at least have the security level provided by the PSK.

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

## DHKEM(Curve25519), HKDF-SHA256, AES-GCM-128

### Base Setup Information
~~~
mode: 0
kemID: 2
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 39516b2f05e9757e21331c6f2019045f52cee01a741e2a8b50380408d0717fd9
skS: eea949550bb218c921ab85cbc5003f4ef6257db1b47b7ed63a223c8360ef81e3
skE: a1f7746c45d1a0eb72b996e0e7ecddba0e60a583a5e143796981101a3aaf8966
psk: 3564623362383061383163623633636135393437306338333431346566373061633
1636338303636333964303133353738343937343061303364616464666339
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 14fdb807c79fb787d47890d502bce7c335d0809a053b9287e30fc608fcfc9d26
pkS: 6eac89bc5d63e7b40c394a4218b6a8203803749f95fca2369611ed41afb97e06
pkE: 0454a5a10ecaf982219eae4b5c36bc3e1606813caae1d262528396c60de44e3d
enc: 0454a5a10ecaf982219eae4b5c36bc3e1606813caae1d262528396c60de44e3d
zz: 15178ef77262b0468ee828a6da4f2620434a9edfdddfe9256ac53f8c6b7e575d
context: 000002000100010454a5a10ecaf982219eae4b5c36bc3e1606813caae1d2625
28396c60de44e3d14fdb807c79fb787d47890d502bce7c335d0809a053b9287e30fc608f
cfc9d260000000000000000000000000000000000000000000000000000000000000000e
3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b85555c404062
9c64c5efec2f7230407d612d16289d7c5d7afcf9340280abd2de1ab
secret: c5fdbbad5c72ed703581bbcd3fe890a7ed46d6bf00c73c9755bffbcd6744f22b
key: 11cf34f93b3d1e8f2e36f91c5a2d6818
nonce: 23acef669d7f3bcc98f6d0ab
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 23acef669d7f3bcc98f6d0ab
ciphertext: 13fc68aef8e2c4591a0dd92c01ffe9573314d881cf71dd5708644ee71848
18e457de3b4d51eb1deb4f0beb35d1

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 23acef669d7f3bcc98f6d0aa
ciphertext: 2d7f0e514ce14abf93b0fcc34347e20d23008465c6f98aedc1f1fa806bfc
07708ff20ae9989bb770b18493f3af

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 23acef669d7f3bcc98f6d0a9
ciphertext: 3fa07d648ba64a5dd3816c2a512937c2a58b8428a1067b5ac15841541d5c
6d28cd415faba7d552d606d6c5f48c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 23acef669d7f3bcc98f6d0af
ciphertext: 3aeeea18f990589141df055a90f382a8096dbdae8f912291cfeff475ede4
f9b023c3ce88f499f5a2dc44454241

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 2
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: c903da955074d28232e6ba339f4852abe9b4cb2383dce60ca88d6d14b16fc3e8
skS: 924b59aae3bcec73b8c2533513dfb0059c19e4ec8bd78e94cae7b73c2b8fe037
skE: f35123835eb4d8858e7f01c81840ec21b30d444c23f2e26c67f299e0c06df023
psk: 3564623362383061383163623633636135393437306338333431346566373061633
1636338303636333964303133353738343937343061303364616464666339
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: f1a4ebd32e84fe2614ad0a7270fb7dff328f275dc8b9d54c2345e5518130b42f
pkS: 6b5dcac8182954357e45a6f9eee722cab9509920441ecc3d2ada5d13f5dbda42
pkE: c44b2464180ddc477d579b824b2fc7931b0f59138f115af395443fd692ae1661
enc: c44b2464180ddc477d579b824b2fc7931b0f59138f115af395443fd692ae1661
zz: 8d669b593e5bc3bbdbde2a95ae892e68976a859136ebd77ea41a09d16602db57
context: 01000200010001c44b2464180ddc477d579b824b2fc7931b0f59138f115af39
5443fd692ae1661f1a4ebd32e84fe2614ad0a7270fb7dff328f275dc8b9d54c2345e5518
130b42f0000000000000000000000000000000000000000000000000000000000000000e
ca994d516108a16db86e155390f3c3cec6f0aff60ade1ae9e3189140b0f3dea55c404062
9c64c5efec2f7230407d612d16289d7c5d7afcf9340280abd2de1ab
secret: 640de51e7b5ae69424e64c931d7f28d9d495ca9c4c2ffdbc5c9f8a611dfa58c3
key: 53ade960668aa4983b4475e0273c2d9b
nonce: 86b6e1851b3de8f5793da87c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 86b6e1851b3de8f5793da87c
ciphertext: 680566a43d511463e8a64d81e89c9a2caacaaa268c815a864bbd4bd67edd
5300e1d1257f89962fa473c0e41918

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 86b6e1851b3de8f5793da87d
ciphertext: a990169c45c7ef5cfaf1ee040f64e946b71424ad74165f59ef13ffe752e9
ea6d5e7e6edd366fdb62f76840b221

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 86b6e1851b3de8f5793da87e
ciphertext: bb6acca5ee76f39ff44feea5a6d8d0b0a94f71767dffb24c023d2ba908c9
4c27b14ea1d1aa132088cdd801c7d0

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 86b6e1851b3de8f5793da878
ciphertext: 001a42b2883eaf05954a784101575dc382f0fe5e61ea2e32dbb80d788ec7
3506e31fe0dc67ef7413e34af45c94

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 2
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 0a08a01d1f7033200bc94e8a551f7ef0b1c076940e2a4eb6d63df9cb03f65b66
skS: 274e3083ca1c7462f80b2586b811e8058f7d5077aaf57829804a632555bed1a6
skE: 5bb3e4aa6deff90de795b4b0f8dde7fa315a25d8b1a372324b60c09142ae8790
psk: 3564623362383061383163623633636135393437306338333431346566373061633
1636338303636333964303133353738343937343061303364616464666339
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: fcc53e696c9e98508909c461fd173c315d6fbdfb8bc5145bc5e14d8e8bdc891b
pkS: 8dce67e0beb5cbbba1f02f527f6bdf21d739d95f8236c408a231e7c5994e987a
pkE: 8e0385b6a817d31fa221a24a743d52c2f28babc3fd9c472b465ab3c554eb8705
enc: 8e0385b6a817d31fa221a24a743d52c2f28babc3fd9c472b465ab3c554eb8705
zz: c23a969bb27388e124753cddb87b961dcb8ea69df6ce06e2c38cf6b48a5baa0afcb8
87a3b59ea470e088c0c2438d52a6d62165edc7a574282b5600f85eb77920
context: 020002000100018e0385b6a817d31fa221a24a743d52c2f28babc3fd9c472b4
65ab3c554eb8705fcc53e696c9e98508909c461fd173c315d6fbdfb8bc5145bc5e14d8e8
bdc891b8dce67e0beb5cbbba1f02f527f6bdf21d739d95f8236c408a231e7c5994e987ae
3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b85555c404062
9c64c5efec2f7230407d612d16289d7c5d7afcf9340280abd2de1ab
secret: 4daa0f01aeb98cbeaf4df37951738703e302377c3e67781a82215e5cc08c1015
key: 37d7bd91850532cd99a7ef92005385e5
nonce: a4d99fcff465f605298e42ed
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: a4d99fcff465f605298e42ed
ciphertext: 819dde5d20c32ab17b951ec95193e487e859e66f85b51ed8fe26ac1ef8ec
6a81f58e36a33bcfc753b6f99f6b85

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: a4d99fcff465f605298e42ec
ciphertext: a74432530cedd02492e2a3b634e7c60e1be96099d00dbe7f1a98dad8cd0c
8ded65814ee41364a14f38abf71f36

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: a4d99fcff465f605298e42ef
ciphertext: 83097210c9db0f6523f0fae2b501a8e0d2c0f07c051388aa8fdb1c7bd773
6da75b89b296fe9e1132a9cff06f82

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: a4d99fcff465f605298e42e9
ciphertext: 37bb31e8bdc4a604610a4cd9aa0bbf6b581cf3123b62455c41776b335f45
be8cca0d34a5cb1b2f18cdf7befd64

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 2
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: b6510cb5e716a9a482b5415c53c0c03cc2843036660a4a41c0ae5ff2153da8bb
skS: fae69766a126d64f01d0e7d98cd6ec3c070e7adbaad5175cdb85c726e645fab3
skE: a6b6bbb312dbebe9845ad17276d00177665a566a678f23e3cdd90246d6d7bc1b
psk: 3564623362383061383163623633636135393437306338333431346566373061633
1636338303636333964303133353738343937343061303364616464666339
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: ad24daab7cf5292112fe0c88d9b718ba1c13b9de117a562d81143e5cd44a6a34
pkS: 8fa928b39e2ac2e9e5169c82ac4858ed73e873b3997bd1c9f959b1536770bd70
pkE: 565332007b0fa753345902168c10a0ada434346dec1043f590e7cf2b65889825
enc: 565332007b0fa753345902168c10a0ada434346dec1043f590e7cf2b65889825
zz: 86be5ab07841ec62f86a9229b7c3a1ccc273a984aba4d889bc614ae781f9c42fe23f
a8affd75d61a5af02592b599f6f701a967d8d34317c0d9a3a1b3ce5fb95c
context: 03000200010001565332007b0fa753345902168c10a0ada434346dec1043f59
0e7cf2b65889825ad24daab7cf5292112fe0c88d9b718ba1c13b9de117a562d81143e5cd
44a6a348fa928b39e2ac2e9e5169c82ac4858ed73e873b3997bd1c9f959b1536770bd70e
ca994d516108a16db86e155390f3c3cec6f0aff60ade1ae9e3189140b0f3dea55c404062
9c64c5efec2f7230407d612d16289d7c5d7afcf9340280abd2de1ab
secret: 0e360737217bf54c4f9660414ad857dfcf0a2419aca181bd8ecdbe8dd1563a36
key: 9b59048c7fa79046b30866f60a14c7b6
nonce: 9e1b30052d1260a35b439162
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 9e1b30052d1260a35b439162
ciphertext: 7a9b7ce26eb18ff13f34e4e05e3c0064737c06000ffb9dd900f1eb63abb8
39f17af22009e38944bdf7842f6ce5

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 9e1b30052d1260a35b439163
ciphertext: 0d4423c76fae6e6e38ef9b5768c16238ec0ff20014ac0d84b49d87cd0056
2d05ef67ab442b375d51bd1e931f62

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 9e1b30052d1260a35b439160
ciphertext: 9f635ce5297959256dbcdb1acbbc7bb5a8f1100511090232e2e8f3d6ee4e
067a2c4311401b5f91ae7f5c0a99dc

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 9e1b30052d1260a35b439166
ciphertext: 5b0a5bc354a87a07226abf016e8e689a6316cb6c42fa3506dedba813e042
9b8e3cacc2e6d311e900d6441f36be

~~~

## DHKEM(P-521), HKDF-SHA512, AES-GCM-256

### Base Setup Information
~~~
mode: 0
kemID: 3
kdfID: 2
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 01cf7db2e78823889fa5c7f45ff20c845e9c870861ba51cef7f6546ec7baa4d60cb
db3586dae794bc7d4d9c6cb54409be24624f30c745c75244316a1a9953254c6f1
skS: 009ad3116e7c9d3e09eab465eeae0712c29498d6c5a8b144410aa1ad3f19942f88b
9ef89f77c33b14fd4bc23cab7e4154b1702d441d872d07fed197f10e6f29c6c82
skE: 012bbe591757f8aa4e5640297ea45b669ba14ac5047d04d0ed136f74512ba916149
b3bef43d64bc2e47e17ae9c9937dad167dd214c6aaf4a60c38140a9bfbf67f3ec
psk: 3564623362383061383163623633636135393437306338333431346566373061633
1636338303636333964303133353738343937343061303364616464666339
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04003ff813033df935e1ad38eb47258b8f5634fb491437b82b17563d5910117f1b5
193bb7be71fb8413cae9d538cbc9dacf792864941ceaa588cef0dbbf27e81495430014cc
f9aca4bb88f6a416ca3339579b29a038c2124b2f9dfc9b306eb57b77961d6ad444daf3a7
9be9088ff28624781cb93a87d3873f7d6ae11ca2195b0cdda5c6ed8
pkS: 0400630359fc1cbb8257504d8a3242538558a82b0c826a29fe95f8ebdc0857067c7
7c0f8cc8dda2e98f3313444a5efda1ecfd47d5da68fe2ef26f729de47cff529dfc000a66
ef90d5a1d0640a61d49c614336e1734142d3586db9c2dde39a0f5269f62e533e8763f9e9
cd727df3c7256224babcdffd5d18d0cbfeeb7e916cfff9f68cb02a3
pkE: 040025938c1a2d444a8dfc093f8e8d8c23a8269292bb89e1852e8298f8b97f86cc8
f5f21a3bf038916ccd164328fcdf34d06ba0f574c1899866d489e61c2c81aee071501037
45a8d7034287fa0c8051d499a60ce53844ecbdf088d14ff4bf3e53c12ad4182edf062103
d67bfb722c9d24e0d3b23925b8e819006dfb1eeb0d2390265b25a4c
enc: 040025938c1a2d444a8dfc093f8e8d8c23a8269292bb89e1852e8298f8b97f86cc8
f5f21a3bf038916ccd164328fcdf34d06ba0f574c1899866d489e61c2c81aee071501037
45a8d7034287fa0c8051d499a60ce53844ecbdf088d14ff4bf3e53c12ad4182edf062103
d67bfb722c9d24e0d3b23925b8e819006dfb1eeb0d2390265b25a4c
zz: 007a7d4668515bc876fc67d936e1e4f76ae576c50207eaafd6cef8bc9153d97115e5
5233cd67fbaa62f04452b959617e7a3bbd52239f5a3dfce6a8b7a89e52faec33
context: 00000300020002040025938c1a2d444a8dfc093f8e8d8c23a8269292bb89e18
52e8298f8b97f86cc8f5f21a3bf038916ccd164328fcdf34d06ba0f574c1899866d489e6
1c2c81aee07150103745a8d7034287fa0c8051d499a60ce53844ecbdf088d14ff4bf3e53
c12ad4182edf062103d67bfb722c9d24e0d3b23925b8e819006dfb1eeb0d2390265b25a4
c04003ff813033df935e1ad38eb47258b8f5634fb491437b82b17563d5910117f1b5193b
b7be71fb8413cae9d538cbc9dacf792864941ceaa588cef0dbbf27e81495430014ccf9ac
a4bb88f6a416ca3339579b29a038c2124b2f9dfc9b306eb57b77961d6ad444daf3a79be9
088ff28624781cb93a87d3873f7d6ae11ca2195b0cdda5c6ed8000000000000000000000
000000000000000000000000000000000000000000000000000000000000000000000000
000000000000000000000000000000000000000000000000000000000000000000000000
000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000cf83e1357eefb8bdf1542850d66d8007d620e4050b5
715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a53
8327af927da3e490ce9df289fea4615a6eef004e5cec7a77f0f0478e663643a1ab75945a
0082e5b91ad84905c1632605d8377ed3d2cb688cf352d67466c37bfaa08c8c765077b
secret: 4770a7d95b1a0326e5fae35e1d3434fcfacca6c0dacbbf9cc7d1d6c983e146bb
5396b6fe3c699004b33e49c8077ca672a6f0c0666d6ed9c2bb32ad708ce04a4f
key: 4ecae7e036312dafda581ff13ca74aa62c564116f50e1125d1bfbd134e1f66dc
nonce: 594baa22942e8a065e8183f0
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 594baa22942e8a065e8183f0
ciphertext: be580294672fd350dcb8da1b9246821407c4b02e32efae0150ef6eb76a97
0b6c0cb2b2a594a9719ee6e3ef0549

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 594baa22942e8a065e8183f1
ciphertext: f97e0702b831062499dcb56fa4dbdd7725dd0a4afc8338d0f61c6daf7fd1
1bb1b4d2009d4d40abcd1d3170050c

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 594baa22942e8a065e8183f2
ciphertext: 5e68db84fc05d2c3b137588bc54a5fc374e4c27827b2c1c7e555cce29507
84be624a0631285c7a3a05f1ca517b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 594baa22942e8a065e8183f4
ciphertext: b682800ccd28b82fa7f15275647b3a1c0998e46a5be5772071a4865ce0be
e99631fa62afc130f2e1fe8fc225c7

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 3
kdfID: 2
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 01244fd7a0d476f49b7450267d272ec0f34c6a46e817df3cea2953e01fc43851a40
d73e07bc3a36faaa7ee39505dc451eb68e86a4f6716e02f4dc10296e1bb3a9252
skS: 01b61d8ec4cddae3fa76d941b05587b0a5afe0323ff8d7086178e4b4dbd2bfe07e8
3299fd8a232e8ba07b608b32907a626b4bc054b0b7d7bb56c7b7f7b4b9728c808
skE: 016c462ff76d276265231671f9df46cf2ae4b621f3f0e842ec15f6063ff841a0194
24ce5c39ddee352b0cc15cf2782b9b7aad0c3f5091d324c43de608c2464d4ef2e
psk: 3564623362383061383163623633636135393437306338333431346566373061633
1636338303636333964303133353738343937343061303364616464666339
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0400606978b77a55730536aabb3ff81b596466b1f0ecfe13c6a9c4f9633cb99662a
63019387cfca443c0d342b7e0b580dd88e226daa5c50ce0ee7fcd4d545f90868a6300746
fbdda2b4402c315b8b62b4d4aa9b4f9f818107c3bb5b4d4f536c6245f4f061c5dffadbc4
ff38c6b6577962993fc0859f5beeff052f63b94b93703d599bac13e
pkS: 04008b2f8d9d12b888774f70ee6722025ebd0061910cac04d6b447879dd2170c176
39a20cdff247560af7ff8a1cd7767de74fe5712cb18197171d14b8e4a030c0edb190199a
5fcdb5b15e036e9989eab241b050257de70bc963221dbbdd054dfac2f6557248ba14c635
a5de2a8b06b6ca54182fb6c065b0ddaeb157104ef78a5e1dcb97640
pkE: 0401464b59282a6b88623ee6449b1132a252bc7be17d59e6731c69f4ede2ff357b6
8e973f528ad45e087745642a06fd7e6292a7b182860ecdcf10eb6cbe0ec347ed07801f49
1c84614cb63ec0e5dd6ab8f4f52906b8126f8813682db6365dc7101c4069823ecffa5c80
b5b2e62f2c66706195b65ec415f6d64dab4cb716885a7c0945a071b
enc: 0401464b59282a6b88623ee6449b1132a252bc7be17d59e6731c69f4ede2ff357b6
8e973f528ad45e087745642a06fd7e6292a7b182860ecdcf10eb6cbe0ec347ed07801f49
1c84614cb63ec0e5dd6ab8f4f52906b8126f8813682db6365dc7101c4069823ecffa5c80
b5b2e62f2c66706195b65ec415f6d64dab4cb716885a7c0945a071b
zz: 01d325aaa842b0d08c52203e3de519f5822a91a4fb6b84f7a22bdbaa58738a8b0c60
578c76fda19a9dbfd8bdcebf5885d80723ca6eb512738b40e166ac234bab931c
context: 010003000200020401464b59282a6b88623ee6449b1132a252bc7be17d59e67
31c69f4ede2ff357b68e973f528ad45e087745642a06fd7e6292a7b182860ecdcf10eb6c
be0ec347ed07801f491c84614cb63ec0e5dd6ab8f4f52906b8126f8813682db6365dc710
1c4069823ecffa5c80b5b2e62f2c66706195b65ec415f6d64dab4cb716885a7c0945a071
b0400606978b77a55730536aabb3ff81b596466b1f0ecfe13c6a9c4f9633cb99662a6301
9387cfca443c0d342b7e0b580dd88e226daa5c50ce0ee7fcd4d545f90868a6300746fbdd
a2b4402c315b8b62b4d4aa9b4f9f818107c3bb5b4d4f536c6245f4f061c5dffadbc4ff38
c6b6577962993fc0859f5beeff052f63b94b93703d599bac13e000000000000000000000
000000000000000000000000000000000000000000000000000000000000000000000000
000000000000000000000000000000000000000000000000000000000000000000000000
000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000f19e7afbe93b9d8b9837fe0a40ada462caf9a031824
8f66dd7832fac65a58dcacbf170937f825b35d22fd19125483b1f2f6993549423617d8ab
9f65322d627b6490ce9df289fea4615a6eef004e5cec7a77f0f0478e663643a1ab75945a
0082e5b91ad84905c1632605d8377ed3d2cb688cf352d67466c37bfaa08c8c765077b
secret: a2ff54181b5c15413a7ead08e580b0c079bfadbfd0ec947b12df653783bb826e
04e1b078bbf7624756dfab4248b662f652eef613e70b2f8da7416c40d652e050
key: 24065fd86a68c21bcd1f69eea7d9624f15d3778f0c96c2ff8a03c04d8b5e6846
nonce: 51fb39ad98f3a339a26a764e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 51fb39ad98f3a339a26a764e
ciphertext: 9411c8988f7336d65b934ad5edea81b657f341d1f1e5d41bb05fa19903d2
1f4c7f3f6462a0c5fbcaab67020efc

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 51fb39ad98f3a339a26a764f
ciphertext: d8c98f96bd510b91c120a517fcac300cee5af2eaf3478cf08b06279c12fb
46acde7f83012f0134f0329132217a

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 51fb39ad98f3a339a26a764c
ciphertext: 361e7edb6a1192913e60b30fc058ae2d2af118503a6c053b956e4259ffd0
64b7bdbbe4451e74528b14f15bd44f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 51fb39ad98f3a339a26a764a
ciphertext: 1e392fcdf179a034b0bb34062fa359dab4bde3093600d7739f0b30d31b0b
6f831c6440c8102eb5a683cb78dde5

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 3
kdfID: 2
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 0167e7922fb57fe3a23622c078e92353a1108e6bfadbd977455db6a0bbf61f42ea4
6b880d138a95e14c3aaa1fb8625229990e275126e00f1fb49aaad09e18fe097df
skS: 01c1b5c8c23e3c076ad3ff2334981aea232aeeb884498c9b50140e425c3fb98bc4c
1a37368596ea2183e48cc5f948bdd53eab21eb475494907dcffbadcde086afb9b
skE: 0064ce1aab784114ca4e8da89951b72ddb688a8f38d49fbede30acc8b48f16bb80f
1ccc2e5d4079988b23c8042ee1f971789562affd99c7a09044c2f4499553f3c78
psk: 3564623362383061383163623633636135393437306338333431346566373061633
1636338303636333964303133353738343937343061303364616464666339
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0401f99b3daeec2adb4d9dc34fe981c761083890a9c446c1debbfffca9c35db09e6
78c03d5c062b13854151034d65e121123a6eb1e5f2e475ac78e13c56121a0fbe43801c6c
fc7b845f902d2a036aa89dfbd3c1ae148f278b71f83d68bc9cc4ee65e43c484f19456663
ac3f04c1d824b4dd0edce454b36d933235f6025968468ec53bcb275
pkS: 0400b04e91f3a4ae9ca6de1d1df6642685100b87d667c39bb39ef49c5b8da5ca33c
d54ce4a3fda1cc02295f501d21ff858f005731288b5095a0a9ea18e468890ae3f1a00b5f
b6a0b5ad28e0bb9285f86adc92e4764cf71da57cfc9315b9c661176b2f5248b9bea5ca66
f2edfb422a755795d9f2ff91e9d36c3e1996de867c8f151c13ced3d
pkE: 04019290abae722dd3a5dc603c3baec5275a7490fd85d779132dd00fbe5876bece2
d8ae51aab0ebd48ed43e0e017316be0c6e1e8290589b59c17670979586e6fea2ee300467
d9d8c8fe93da9961d25e569cb87937666bf4abdf9493edb14b2c64e41d7b4b695f63f940
f51c9f8b8921f713575978140cadcae55f78175fb14fd6dbfa7bcb0
enc: 04019290abae722dd3a5dc603c3baec5275a7490fd85d779132dd00fbe5876bece2
d8ae51aab0ebd48ed43e0e017316be0c6e1e8290589b59c17670979586e6fea2ee300467
d9d8c8fe93da9961d25e569cb87937666bf4abdf9493edb14b2c64e41d7b4b695f63f940
f51c9f8b8921f713575978140cadcae55f78175fb14fd6dbfa7bcb0
zz: 002ae310e807be1850299dd1bc9e606de09ccf62eed02abd88793fcdf22e2008cf55
80108cbe9c5d4f813e5f560bfc4964c2d932700833ccf4af6eb4454457d1ffa70153c4d1
23d448a732603b37a84ec20cae6387477f0005e9024a29b20843dadb7843c198c2688532
3335e6335496e12aa522490ad3cba3744fe848b0357292f657ad
context: 0200030002000204019290abae722dd3a5dc603c3baec5275a7490fd85d7791
32dd00fbe5876bece2d8ae51aab0ebd48ed43e0e017316be0c6e1e8290589b59c1767097
9586e6fea2ee300467d9d8c8fe93da9961d25e569cb87937666bf4abdf9493edb14b2c64
e41d7b4b695f63f940f51c9f8b8921f713575978140cadcae55f78175fb14fd6dbfa7bcb
00401f99b3daeec2adb4d9dc34fe981c761083890a9c446c1debbfffca9c35db09e678c0
3d5c062b13854151034d65e121123a6eb1e5f2e475ac78e13c56121a0fbe43801c6cfc7b
845f902d2a036aa89dfbd3c1ae148f278b71f83d68bc9cc4ee65e43c484f19456663ac3f
04c1d824b4dd0edce454b36d933235f6025968468ec53bcb2750400b04e91f3a4ae9ca6d
e1d1df6642685100b87d667c39bb39ef49c5b8da5ca33cd54ce4a3fda1cc02295f501d21
ff858f005731288b5095a0a9ea18e468890ae3f1a00b5fb6a0b5ad28e0bb9285f86adc92
e4764cf71da57cfc9315b9c661176b2f5248b9bea5ca66f2edfb422a755795d9f2ff91e9
d36c3e1996de867c8f151c13ced3dcf83e1357eefb8bdf1542850d66d8007d620e4050b5
715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a53
8327af927da3e490ce9df289fea4615a6eef004e5cec7a77f0f0478e663643a1ab75945a
0082e5b91ad84905c1632605d8377ed3d2cb688cf352d67466c37bfaa08c8c765077b
secret: 5b6235bd3622027add71cf60f17b7673541ecb2bbe49085baf10ebe89134ab64
11bd0b75b4621ce47dcd1649700c2903eb5629edd18ee585245123cb2c450b69
key: d81f29eae626b1d6de7684dcf8bf9a385155836eb6cc8cfa39f4ac790948967e
nonce: ca84d6c140a4f270e9af08ec
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ca84d6c140a4f270e9af08ec
ciphertext: e93a30618031c82fb2f2396e56eac0d6ccb7d8f9ade21e8fadbd5f994b71
4975e9d4a3b58d2c768f51d4d5f0cd

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ca84d6c140a4f270e9af08ed
ciphertext: 3738ec9417ac07e1e1c9ee6d0722d74972ed3c3020a5b44b495ecf576e95
0291d06d0f0f73bb6844831f130ed4

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ca84d6c140a4f270e9af08ee
ciphertext: 49bc86ef2ff0653da3a1099b15efd56aacfa80361c819ea82e1eca24a657
69dd67982ab0467e6574907a0e1d73

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ca84d6c140a4f270e9af08e8
ciphertext: 65d227ce7b5acd1038bfbcf85ecdc042e2531195c49c37dc74eec2c2d3f3
cf036adb4bfbac222267748263eb4f

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 3
kdfID: 2
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 018ff7b8d424aaf0ed811739a1980fbac4a4a788d856951b30252ecf87bf4786f6a
a517c5871a41b418b815e5c7a764e43288a0e398cafb1a11f84ddae80f1fc6eae
skS: 001c70b0b9c82580dd9ffb1686a4c1ce8d5d54e669905d2bf91c6e40b81605bae50
9d22a262435100f2da38a40094bdaabd88ec9a548100274108c0549aa88f0647f
skE: 01c2e688a75c6f16702a9053d5fddc6ed0b848ebc19a7312ec6d995d8537c0480e9
5bad4886c152cd156777af7b9d2b915ea017668fb462d3cb777a83ba5fb3cc941
psk: 3564623362383061383163623633636135393437306338333431346566373061633
1636338303636333964303133353738343937343061303364616464666339
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 040073825b5a6284f6e024a1d1fb192645e8af25e62f95f72d62ff36dc8ed4de4c5
5d3dc48fbb3cb747c766b024f03fd9cb0f70bfe08529389e18d4a26fa62c1124e3e01988
10d300f3a1ae823224013e6ab198195375c54c6df5ef6ee2de9f884735e01d0bf023e518
e81759ed2d4c3de949b9117c39cab6186d4c8a21d6271cbf88d073c
pkS: 04007b742d25deaf50156f092ca17b3ce582a77da2db3be658e5e8d1df40fa83ac5
c5e5d673249d1f8cf678c4328dc09718c232850c18ff99dd87e15910b49825c321200e6b
6cd8010792f5be0c01079a87ca1abc03a9567674a034436a5fd7cc6ecf6ea54c92d1ef0a
240f1e407348f69cda753f7b6ed24ede658391612c1c56c778f5ac4
pkE: 0400e6201790d044da8ec517fc3b427e8f45039dcf45268b1b542e944e9aa30c8d8
0efd5b5336ae3a8cc5954d3cfe6f8fc245b9de6dae80d0976568f3018e5e55c572700c0d
399df6f437ed1a002100da5fee7ecbe22f457e296ea896f160b3d8240c7c4ff8b32f9712
2be011bc7d896e76a1ace94347f2260db92e64d523578b96c1f93f4
enc: 0400e6201790d044da8ec517fc3b427e8f45039dcf45268b1b542e944e9aa30c8d8
0efd5b5336ae3a8cc5954d3cfe6f8fc245b9de6dae80d0976568f3018e5e55c572700c0d
399df6f437ed1a002100da5fee7ecbe22f457e296ea896f160b3d8240c7c4ff8b32f9712
2be011bc7d896e76a1ace94347f2260db92e64d523578b96c1f93f4
zz: 01d8c0c1dd80d293c21d47b9702adb3b62822216294b5f5b1f42c80f9a520bd4388a
4910d46faf98b6a70261165258584bf5e2e3966f89e3063e118a0ce2d15b8b910157e379
8b86b0a6bb49caf0ab4622627652f8dde2ac7eab1a517a02e688a47eacacae285657000e
9cc98025d6f06ff5889ba5f9e44233d560bdb4a19c1461236dfb
context: 030003000200020400e6201790d044da8ec517fc3b427e8f45039dcf45268b1
b542e944e9aa30c8d80efd5b5336ae3a8cc5954d3cfe6f8fc245b9de6dae80d0976568f3
018e5e55c572700c0d399df6f437ed1a002100da5fee7ecbe22f457e296ea896f160b3d8
240c7c4ff8b32f97122be011bc7d896e76a1ace94347f2260db92e64d523578b96c1f93f
4040073825b5a6284f6e024a1d1fb192645e8af25e62f95f72d62ff36dc8ed4de4c55d3d
c48fbb3cb747c766b024f03fd9cb0f70bfe08529389e18d4a26fa62c1124e3e0198810d3
00f3a1ae823224013e6ab198195375c54c6df5ef6ee2de9f884735e01d0bf023e518e817
59ed2d4c3de949b9117c39cab6186d4c8a21d6271cbf88d073c04007b742d25deaf50156
f092ca17b3ce582a77da2db3be658e5e8d1df40fa83ac5c5e5d673249d1f8cf678c4328d
c09718c232850c18ff99dd87e15910b49825c321200e6b6cd8010792f5be0c01079a87ca
1abc03a9567674a034436a5fd7cc6ecf6ea54c92d1ef0a240f1e407348f69cda753f7b6e
d24ede658391612c1c56c778f5ac4f19e7afbe93b9d8b9837fe0a40ada462caf9a031824
8f66dd7832fac65a58dcacbf170937f825b35d22fd19125483b1f2f6993549423617d8ab
9f65322d627b6490ce9df289fea4615a6eef004e5cec7a77f0f0478e663643a1ab75945a
0082e5b91ad84905c1632605d8377ed3d2cb688cf352d67466c37bfaa08c8c765077b
secret: ebac42c5954a94acb80e36ad504a9ea835704cc0d6a12c54b8f8f16739e0f673
292766c0a9178ebd5483c4b08abc80f9c496fef07fce5e580a262e5411f74cba
key: 4a3b4976b783d37f708b3be231b4dc7d03d52ddfc4499eb2dbd74e08581c20b0
nonce: 855531ca5f30cd5b596148be
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 855531ca5f30cd5b596148be
ciphertext: c9883e246c7619387b29d1bd40af6b6aac0d223a5a28570b02eb86a337b7
e09450c20d131cebeab6abd704df2b

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 855531ca5f30cd5b596148bf
ciphertext: a2e0f8a4c52f3f0de2edd67c91d8e4f36e4f8ba2eec9226e96386b784970
b9b21e7bf1a574500e5a2254c96eb5

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 855531ca5f30cd5b596148bc
ciphertext: 2d4ea06f7c024df4bddc0b2755f115f3582edd149aaf3134870877c3cdc3
3b1262e39402296948799835712fb9

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 855531ca5f30cd5b596148ba
ciphertext: ea9612bea28e4e3ecabf9194953d0c7da39ea9a7bf361d29f224b18fe053
47408d9381d1c332b61e2e01d94191

~~~

## DHKEM(P-256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 1
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: efd90477fdb7b8f60357eec8d7ae348fef38b0c55c3298c09caf9d575990bd22
skS: 2ee3b88417a20b5fb0a527fefaae4066a6449d2d75bed96fa2478d58f300c411
skE: 2118dc1de1f6578b3576b4e6996fa6517ceb28a403fce626c8e0d430bd571f8b
psk: 3564623362383061383163623633636135393437306338333431346566373061633
1636338303636333964303133353738343937343061303364616464666339
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0441aa0ed8d749bab7f9a2ed9515ea60ad5b5cace45710f4ce6bf99bb44a1069d8a
9c12ef2f514fb1c9185c8db167c821b2aeb38d1f821ba1164101c85ede7ee13
pkS: 047a9f60ef11a46a211fa3ca38c14430a282cefac5b90866918d64ffad2cdfe7d41
fed52aaea83f703407ed9bb3db950023a1accb689ba91b5743cec9d4680d080
pkE: 049904661176dd864002718fee7b491330d54f45bd37172b6b9ae8038cce88b9f9f
ad47829699477de2fb014827b4a8e7f1e4a870304aad3d7986d68d35cd07ff6
enc: 049904661176dd864002718fee7b491330d54f45bd37172b6b9ae8038cce88b9f9f
ad47829699477de2fb014827b4a8e7f1e4a870304aad3d7986d68d35cd07ff6
zz: cd6e7bb5ff8c134f2a925e9ca022e65f5b487321bc3e576f377e6f01236a1bbb
context: 00000100010003049904661176dd864002718fee7b491330d54f45bd37172b6
b9ae8038cce88b9f9fad47829699477de2fb014827b4a8e7f1e4a870304aad3d7986d68d
35cd07ff60441aa0ed8d749bab7f9a2ed9515ea60ad5b5cace45710f4ce6bf99bb44a106
9d8a9c12ef2f514fb1c9185c8db167c821b2aeb38d1f821ba1164101c85ede7ee1300000
000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000e3b0c44298fc1c149af
bf4c8996fb92427ae41e4649b934ca495991b7852b85555c4040629c64c5efec2f723040
7d612d16289d7c5d7afcf9340280abd2de1ab
secret: 15a36bf657d3b3b4eb355d6bf2a595f710e4a4da37d2710964167ba8029227ee
key: fe8f6e7d61f81dc4cce9b185b4343323dcf7eaab8c2ac36239b2a9274c198868
nonce: e61fbe136571b0fa5753e51d
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: e61fbe136571b0fa5753e51d
ciphertext: 8ca64a2de7e35f68444f4fbad9fad274e98515250c46602a775943efc0b7
9ce216005b465620050e465833dce0

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: e61fbe136571b0fa5753e51c
ciphertext: 8c04a6d97f1b43b20b6431ebe5379a3b8fc44bafb74a1d7766c9299fb36d
2f2335321115f550d30a9eabe368fa

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: e61fbe136571b0fa5753e51f
ciphertext: c14f9a30f8cb66a4125a5165efd88fb3cfbf481009a0f880013d885abc44
6c9fce029a44dd0bad9be66ae18fa1

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: e61fbe136571b0fa5753e519
ciphertext: 221884f4ff14f3386e6bfb00f0179bba99da2c5a6a3867078b11fdea39c4
7f088dbdc8f271c842e97f6d048c71

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 1
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 3dc6dc4839c96a68f1a126261a1d6cc31960e3891266ca5793c17fc7c739ec26
skS: a5d6e4cc2f531cd23ca6828a1a2b540f93c40784cbb347fc4b7765beea6d2f51
skE: aba85f04d1cbf29d01d4303378e9e845f182f98d71cda4e7715c9644ab297d15
psk: 3564623362383061383163623633636135393437306338333431346566373061633
1636338303636333964303133353738343937343061303364616464666339
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0466daf2d7e1fa5db08c5c9e176b021f05fb00e39b83248caa25fe098556a7af09e
7107db9259d1c0fc3055863277d830e04022653e543fe9ae5dc48940dd21dad
pkS: 0483d9931c6593bc2099ccbebd36609be5ef89ae4cba94270802e318a5f2619cddc
ac5ba077192db6c834cbcc891f6200ad39dcbd4fbd8acc4e25817d7a10d316c
pkE: 0418234cb6d16fe20481c2ff80140aa3ffe84f2afb6be64645ecc16b76e0be3dbfc
997b53765a3e58a555752063bfbf7fd86bf6b3a72cb65923818114e9a740348
enc: 0418234cb6d16fe20481c2ff80140aa3ffe84f2afb6be64645ecc16b76e0be3dbfc
997b53765a3e58a555752063bfbf7fd86bf6b3a72cb65923818114e9a740348
zz: 1bddb02ead402b3f293503475d98cfedfa1b00b9d41e4b13ea01c2d4df9652b9
context: 010001000100030418234cb6d16fe20481c2ff80140aa3ffe84f2afb6be6464
5ecc16b76e0be3dbfc997b53765a3e58a555752063bfbf7fd86bf6b3a72cb65923818114
e9a7403480466daf2d7e1fa5db08c5c9e176b021f05fb00e39b83248caa25fe098556a7a
f09e7107db9259d1c0fc3055863277d830e04022653e543fe9ae5dc48940dd21dad00000
000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000eca994d516108a16db8
6e155390f3c3cec6f0aff60ade1ae9e3189140b0f3dea55c4040629c64c5efec2f723040
7d612d16289d7c5d7afcf9340280abd2de1ab
secret: 18e7dd273976a38568a1d97d01a0f68ced4b1e680629abb6c147976be2c9a68e
key: b0b09b57b888ab7f5ff36c301bbecf73a10c952f3089b298969894bdb6ec092c
nonce: 293fb9ecc6499ab799f74aba
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 293fb9ecc6499ab799f74aba
ciphertext: eb9679b0cbcba88710858b834d40b320afc2f8b8623cba8eaa198269c02b
3d0649724b93ed9fcb34f98ac91659

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 293fb9ecc6499ab799f74abb
ciphertext: 75e4cf4add98bf9804456210fd623be7911594f91a98f24559e8e9203b4a
be932913bf9d530e83797d430b0adf

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 293fb9ecc6499ab799f74ab8
ciphertext: 43ba4f906914636f47c6a80059e0924db44c2a747af0a4432b476883f2a6
bdc9843538902706188804fa98eeb4

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 293fb9ecc6499ab799f74abe
ciphertext: 3a2cc9fd2ce341bff18b3a55949afca1ad73faf18e6d331fa37a467dbef1
5696b2fea0228808f7bc121ee2b2e3

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 1
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 8cc7881e1438783080f4422f9716929a5d7406bf3eda38ef26298ac1574d38c8
skS: e82f5350eea923aced4a03c5d37da628dd9629f3b4a9c0d69f1eeb0adade6c34
skE: f12bb99fb1adac970c60b1a9e747e0da787b2dbebb9e22a6c9335b1e8944d106
psk: 3564623362383061383163623633636135393437306338333431346566373061633
1636338303636333964303133353738343937343061303364616464666339
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04fcb0c3c6335bc9ef4aaa4e60b2db6ad10dfcce8d27512193cb119b6b71ec8fad6
ac7ccd8c3ce24b05c0e4670461b9968358d1902e1282fd20824928055c63064
pkS: 04a65c3735ebb9d5dd9de125e1a2e0ade33eb590c578e53308412ba444e091c8f4d
db45d965527a7e99ee21cbf35517b3c8b75d2c333623aeab1deef5ef7c0b21a
pkE: 04bae2436aa78ceb08481b3fd7f9104921a84cb1412a9b377db0e333225659b08ce
ac43adc28ba392db9f3a0c2fbaae6fe6b9fef4edcff240ff0b6dfcab383ab31
enc: 04bae2436aa78ceb08481b3fd7f9104921a84cb1412a9b377db0e333225659b08ce
ac43adc28ba392db9f3a0c2fbaae6fe6b9fef4edcff240ff0b6dfcab383ab31
zz: cca4949b43cc9d846e9c17398b3395ab6a268e2f5d733139cd76e2adfc0673874a77
d07c7f2b8b760fc1b6547ebe68b272617a80158ac04fc07398fdef69fe84
context: 0200010001000304bae2436aa78ceb08481b3fd7f9104921a84cb1412a9b377
db0e333225659b08ceac43adc28ba392db9f3a0c2fbaae6fe6b9fef4edcff240ff0b6dfc
ab383ab3104fcb0c3c6335bc9ef4aaa4e60b2db6ad10dfcce8d27512193cb119b6b71ec8
fad6ac7ccd8c3ce24b05c0e4670461b9968358d1902e1282fd20824928055c6306404a65
c3735ebb9d5dd9de125e1a2e0ade33eb590c578e53308412ba444e091c8f4ddb45d96552
7a7e99ee21cbf35517b3c8b75d2c333623aeab1deef5ef7c0b21ae3b0c44298fc1c149af
bf4c8996fb92427ae41e4649b934ca495991b7852b85555c4040629c64c5efec2f723040
7d612d16289d7c5d7afcf9340280abd2de1ab
secret: 614c395e97b3cfb0226a77e9c4095130853c93df9c4f4dec117f7b0204264905
key: e23b412870ea8ce4d178df789d5cf6a4b3f2df9d5b1e9580c95696393d9db28d
nonce: 6a6049cb5c7765a88960c320
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 6a6049cb5c7765a88960c320
ciphertext: 711137546af6a7c7f6a0f04e882fdd7efa097a5ccf8739294bca3439d999
403302a18dd67052860e9fcb30cf94

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 6a6049cb5c7765a88960c321
ciphertext: c68307a9594d7fb230973fb4be22ef9a7c43ccf65d5dc2cde3961893cf27
5985872ee89f692dddeed07c36cec3

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 6a6049cb5c7765a88960c322
ciphertext: 7e25d6df95d22f98f2fb46fccc64411d36c1608d6d858c52d58d09520917
ddb83555dbaab0479dbf0375577937

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 6a6049cb5c7765a88960c324
ciphertext: 71adc526725cb8bec5c149a81da7cdd57ea5a342437dd937514ed4332f4c
e641c8095cf87a21cf53fdbb6ae89b

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 1
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: d1f7d55e5de14783636f2d14d71a1c860f0dbd1aeef7fe39b0b701f515501f70
skS: bb6283dd44d7f974ba50086eaf16d272c20ca2e15c392502e444cf9083a5af15
skE: 80c2f6d99d0bc54d0b3b3ed549f9137c8ebe4996d6686b26fa7d9214adee3062
psk: 3564623362383061383163623633636135393437306338333431346566373061633
1636338303636333964303133353738343937343061303364616464666339
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 040ae36ea457a2df295dfc4272e49b4c3ce80ac2f73a1abd42ff25c9446972062d0
33b99c12f9a122abd1d6456914888fdbd2e5080edd254e523bf00cd48df563b
pkS: 043763d914a4b95237039c08d960efc3c7381ca228ce8e3d945ba4f68c5c44b07c5
46ace52dbc663f644d5d917fb02e7f25d7711855d1396aca7a53a593cf2cd23
pkE: 048f5c15b3888c03ffbccf3b69a225ccf389c5f078f81adf38aee5f2f6d8dfb693c
a56dad6db4fb6dd32908cb3031f735d911b0d08fb79b0ace7b99ddc16d1ea3f
enc: 048f5c15b3888c03ffbccf3b69a225ccf389c5f078f81adf38aee5f2f6d8dfb693c
a56dad6db4fb6dd32908cb3031f735d911b0d08fb79b0ace7b99ddc16d1ea3f
zz: 23d0dbdfd32a8bfdb2cecb239698eb28a797f7173c5885db4d461ecdc7cf55a2efa5
6c4a977fd6fcae64bec282df44e572925274290c2c3ed31e66abfcc5d10b
context: 03000100010003048f5c15b3888c03ffbccf3b69a225ccf389c5f078f81adf3
8aee5f2f6d8dfb693ca56dad6db4fb6dd32908cb3031f735d911b0d08fb79b0ace7b99dd
c16d1ea3f040ae36ea457a2df295dfc4272e49b4c3ce80ac2f73a1abd42ff25c94469720
62d033b99c12f9a122abd1d6456914888fdbd2e5080edd254e523bf00cd48df563b04376
3d914a4b95237039c08d960efc3c7381ca228ce8e3d945ba4f68c5c44b07c546ace52dbc
663f644d5d917fb02e7f25d7711855d1396aca7a53a593cf2cd23eca994d516108a16db8
6e155390f3c3cec6f0aff60ade1ae9e3189140b0f3dea55c4040629c64c5efec2f723040
7d612d16289d7c5d7afcf9340280abd2de1ab
secret: 077842bdbb03e46cfec2c1b5d89a6d22e4fc009ceb9dbb1d0f361f635ea36c22
key: 8d0e8ea21988d7eed10e5b4addba4f0865cd36f87c24181121703eb88961ef2a
nonce: 83af2565d56b585c5380ed11
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 83af2565d56b585c5380ed11
ciphertext: 672a957e804272b9ffb44f180ab8691b786f230cf54c79ebb92d525b082b
134b9482febda1fb1b397a63687c9b

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 83af2565d56b585c5380ed10
ciphertext: c0d1ed854dd5c07fad5f5c1a434e30cac8bf5a4d15486d8dd11e45e7244b
bd66a35ceed694feaae8a543afbee5

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 83af2565d56b585c5380ed13
ciphertext: 3570fcc7f96bebffc27d43f699226c4460f2299d6b03a165b07c94bb5677
6e60d0ff84c38e6fa8f3503c361816

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 83af2565d56b585c5380ed15
ciphertext: 8ea25c2e1e93441779fce40df6b0f88664d1953a250fc9c531bc1dc9b630
39c6061f181e685efb0ed413a0f589

~~~
