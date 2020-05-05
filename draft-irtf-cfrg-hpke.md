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
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/8599f333de354149f86e8f73fe2680d079520a33/test-vectors.json
    date: 2020

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
  pskID_hash = LabeledExtract(zero(Nh), "pskID_hash", pskID)
  info_hash = LabeledExtract(zero(Nh), "info", info)
  context = concat(ciphersuite, mode, pskID_hash, info_hash)

  psk = LabeledExtract(zero(Nh), "psk_hash", psk)

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
skR: c5ff963c2a55b8900f9359598cb7e649b9b53bdaa1c7f2fd73be57d75ad4190e
skE: 1c0698a48523322443f385ae53757e79216240710909dfb318d4e1089c07d19b
pkR: ce84369974e7e916a6689632fa5ead821c041ccd343e0d4de613963938316e00
pkE: 5e2b02f759a3a74d7647303dedbe3f294e98ace44bf8f7f25b5c669a849e6f7c
enc: 5e2b02f759a3a74d7647303dedbe3f294e98ace44bf8f7f25b5c669a849e6f7c
zz: 32ee7c17bf13f1b18e200dbbbbca45586620e298a385b376bc1464c621260a5f
context: 002000010001005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: 61574fbe262a0ae4f6c4f1819961cdf5413c11cb4a66445a399e49af4325f5c7
key: 83ed7977ef1263faaa6a0482e8f805d0
nonce: 2390480018ac0f13dd36309d
exporterSecret:
cda97aa6b37f3c1cb159d28ae22f45a8814fc88bf739cd8b5de7f273e6bb2d41
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 2390480018ac0f13dd36309d
ciphertext: f575fc901ea2ca94c492735d95945201f41218a82b42c69694315b996b48
234e469093b2c3d99e5db88259c1fb

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 2390480018ac0f13dd36309c
ciphertext: 48284097f85b0ed83faf495353b56616433150b418b1498e04330c4b77a1
39f48a784504646745a2a61918433a

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 2390480018ac0f13dd36309f
ciphertext: 7ff9a856ec26637ccbb2f58b7d6940423e6f4469af74b718691bdf6b1af8
d630197622c93e14dfe487a1702ff4

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 2390480018ac0f13dd363099
ciphertext: de55d37d42e65716cb9c3310f6ac073235edf7492660b5595c0a20d04bb8
69ea8053874bca3e4caa9c8c040b34

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: d711cd696fd3b7e165dfaa2a0113c81fde7e0aa51ab0ee8dafc7f14152156e24
skE: 13cb3ed5d9c5cab5e48b3e858bb15b0b3d638310384312f4c6379e339e2901e6
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: bcad7e1f20adaeca8cf65b4e83c28d94f7e12e97b114e14fe52051e371cb823d
pkE: 99525c38cf0ba96f251eb0b259914464bbd19744a82f7f990296d479e2c4e842
enc: 99525c38cf0ba96f251eb0b259914464bbd19744a82f7f990296d479e2c4e842
zz: cf56015806c5aa9a74bf1f3ef63d0676b0c668bd65f2dd97d0edd5c39295dc8b
context: 00200001000101535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: a71ed412c5b4a8f5b75c391b6130b6c8b05e954e177584370edf6a310cf264f9
key: 2c81fff9555bb02cb4b5cb47a618c843
nonce: 7b106553f573a6af74854c2b
exporterSecret:
6971a3ba39ace13b8e0295bb37e2b907ea5b7ffdf2d7253efa54fc690ca6cab6
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 7b106553f573a6af74854c2b
ciphertext: 2d64a4d901f2301bcc34b09912fb2e84964038b134233b3a170c8ccab23b
036b20b3cf1a7e4aa93512522e532d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 7b106553f573a6af74854c2a
ciphertext: 00efceaee742d0038df62ae71b96311c0e9992a079195d3584f2b468d30d
1cfad50e16930b834f42a5b9ea389d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 7b106553f573a6af74854c29
ciphertext: 196d437ed7898c5efc2e1dba2df60cc2d9ebb7b133be4cdc965796204f6e
66be7c6fd8dc7948bd64822d512a77

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 7b106553f573a6af74854c2f
ciphertext: 5d0a4e7a3b959064167e47dafb2f4adb29c004c03022d729874ac62371f8
4c2a79f125c1f734e15ab1f6e5e3c7

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: cb82f0fe23f8cfc18603065beb09f7b8b9ddf61a4d1569bc80fc7b988f50ed19
skS: eedbb5e97c38729706963dfb5b003b01cb7d7056d42b4eb203890d379530cc48
skE: a0921ce591994bb7fecd2f2869cb6e33c043bbbf060dc7f3f52c26c1b4cb5d59
pkR: ddf9f902139803cc75af3a9e69c4eadfb4d497ba602f03465041d2ecaaa2f529
pkS: c502469c46f2437675521fb9c7dbb3d9fce91c8ae63f708551e78a597bc0df58
pkE: 0cf2d01b589540dbd2219cad7f76801d49dc7b01014a662cbcece1846e741c04
enc: 0cf2d01b589540dbd2219cad7f76801d49dc7b01014a662cbcece1846e741c04
zz: 6192acaed6bfeca0262204c9906fee9032da5843b75de2cd9ac6d325d50ad472
context: 002000010001025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: 3bd9c12764790bdfe3d32696fa4e90a062360c0a8872a3edfa5f66a43cecd3c3
key: 6e3f861b242bf9554c73c7c5e74ec7eb
nonce: 50f78707ba96bd6fcf02b34f
exporterSecret:
285334e8a1423ed4980a16b83e456b40f748a7136c65c3d50900d446e4eb8dc7
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 50f78707ba96bd6fcf02b34f
ciphertext: a88b2052f3d8910cb3dab92bdd0d77cbfb990d71dec3a7cebc1cee9d4f84
8e9fdee2ef9bbfd021adb4c9bb9ec1

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 50f78707ba96bd6fcf02b34e
ciphertext: 0e6b4717a260a0dbe2f91d91bba4f22e1c8440d60d5cf69c3620754ef1d7
9901d5642d9201fdf6d8e78f584577

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 50f78707ba96bd6fcf02b34d
ciphertext: 1684cba1184f3c64dafdad5a4d27a89a91e08f8176544d06d521b415f573
8ee286711b628f5e1d53341cf874c5

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 50f78707ba96bd6fcf02b34b
ciphertext: 64228033e0a78f9ce69d31594b10b601af5125d0bade7a245155af0a7be0
d8bc3b66cf5255ca543db72c08330e

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 32
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 2e4146340c7b9b71e517327e96da39c7188bfb272c435db6ddfbc9c38c77fabc
skS: 46b75a55c61840755ba5663698272f03f48ee557f69585f3efce1c1225f01411
skE: 3d5dea3b067d602974d740faf41f14deb4351aed9d84a2ef19029b0937f57c84
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: e968bc245db1657f4319895d0123e6ef7a15f243f01497ef6a917d0eca74f01a
pkS: 75eed8fe25687f4845f28756c0a1cb9b3b34d2021240893f0a81922946fbcb67
pkE: bd360d32222b37d0621395938a4bf4db973f15093537d2ddaf5b4dc36f84db0d
enc: bd360d32222b37d0621395938a4bf4db973f15093537d2ddaf5b4dc36f84db0d
zz: c17be6423489d569d2375d3be94e549d9730c9788313605c94f9eedcce864aa2
context: 00200001000103535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: ecd106041279d65485c9b7632db4030e12c3cb62d1d1039d4fea2803e9791935
key: bfb688d2366ea2791fb312592d4bd488
nonce: a123ba8e429cfb93188ebc1c
exporterSecret:
24afb837a1f6b7659b07f3f5dd9edca12c7fbd14e5a9ae29758db2518a237ffd
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: a123ba8e429cfb93188ebc1c
ciphertext: 443720dfa4c2b81fe42fdedcef45fcc7f8dbe1d765cb36c236badb0eda48
fe1df77a9b63249a588a6b614b5168

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: a123ba8e429cfb93188ebc1d
ciphertext: 664bea9db4d1c691243f369b68bf9f7e147ce3f2a6e595d81e3a509a5017
3123dc126e30893a28a5d3eef1f778

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: a123ba8e429cfb93188ebc1e
ciphertext: 94fdae987223353a67c6cfac8f897d65c1624a8168ba4aafe16fb20b8957
7cf3ec730fa43143379f56b18df9b9

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: a123ba8e429cfb93188ebc18
ciphertext: bac249f38013a0cd1e0c6df74baee01971c6324e52f2c3a32ac09bf04a09
f761ac30f084a452c3200a82bd138c

~~~

## DHKEM(Curve25519, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: ff01ca7c4c6bcb704bee8db3470116ff4de7554d2e500acdd7feb2cb8ba0218f
skE: ff5df277f1465be8edaf318ac6ea23c995e79fd17b740cb065b5f1055be60205
pkR: 1d473c11923cb970b3a65f6b1c03165aba442f0a5cd47979e523608892eee66c
pkE: 88bf47fbdc465e5b9eac21da808eaeabd1e88dfb0fdda7f6b57c940a469c111e
enc: 88bf47fbdc465e5b9eac21da808eaeabd1e88dfb0fdda7f6b57c940a469c111e
zz: ae8c6a5451be4c360dcee046052bb9e9b9cc532a5e3b3ea75ff90d3508d7a565
context: 002000010003005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: 1e13d1d467b787ce909d8df7d9782a27d1a2f91f6b777d1ca5afda8b5dabd22a
key: af37c695f3900219e7d75e423518bc79aeeb697be7dde6c5e2b0917ff9c59e58
nonce: 3ffe5954de6a275ae03e5901
exporterSecret:
acdc0d2bceb5868233b64688a06396316a3361750fe8b3d33cd9456251856331
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 3ffe5954de6a275ae03e5901
ciphertext: b96d09fcc55355c589a29009371e1541847dcf85bb63d54da603f1127e64
388bee89bd88c13d5279f244ffaefd

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 3ffe5954de6a275ae03e5900
ciphertext: 861b2a64c1b34f5b883d514277dc09a2f8c9c0bda6c5507ce06838b315e1
f355903b469fff1b76d144a93de95f

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 3ffe5954de6a275ae03e5903
ciphertext: 81bec05bc5c06131396a3744377edacc493b04aa4e0e600da814a1842fcc
d7a938abef2f651869a361ce21c118

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 3ffe5954de6a275ae03e5905
ciphertext: 36157d9f6e3c5209f86a85971eeacf13ba973b0c6c28130ed93cd5053077
79eadf11c9698f3bfe0d64b03e2a5d

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 005ecacdeabb4e0eba8422073c3e40f066e9aefea7ddd7cf8949e2fc6ad079f0
skE: 1afa9e8ba08e0e281703765ebdaf2df5b7817c009cdf1199a44bf64e4bcba8e1
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 272cb0bd20cc51a6a2c484714a34d5d06136fdcf1b861d8ef49cd39657aca93f
pkE: e57f7768af8ae7785c96779106b79fcecf68bbfef07bb55ef738693f2c3f623d
enc: e57f7768af8ae7785c96779106b79fcecf68bbfef07bb55ef738693f2c3f623d
zz: 958e26a2026b74fa3e759a399308270da7017603cb5e78d594d696c3b873e5a1
context: 00200001000301535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: d1b4a1891d96af496c449ec7b38b8f44ec6d308227266baf1caa3c6a5eb4d81b
key: 2a1b16f48969e6b1e4986bab2dc09229b6bcaa0049cf7ef3063877ad18495ab5
nonce: 341c1b390e2b161517e222e9
exporterSecret:
c4a7843c38734929a19b2c204c1d8693e7147adeb289fd16249ee74397292e0a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 341c1b390e2b161517e222e9
ciphertext: 249ae9a6c4d12ebd647db63f80882691039f12f60f19b22cfcfb51cabe1b
cf56e46e6923d6a6129071a08a9196

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 341c1b390e2b161517e222e8
ciphertext: 683399e2c05dbdd5712f7364de25ec1b0a004d2630218b2012cd25dbcf84
4ca9bb71813ab27e628089d61e6c6a

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 341c1b390e2b161517e222eb
ciphertext: 0d48606e0ccd2ce5bbb4051ddee5958d0b2d8c2374570a75a9fd611504fe
66cd27ec4ae541018a623f4077aaf7

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 341c1b390e2b161517e222ed
ciphertext: c5e810f8cd263cf235f8611f62d2e1dee5e64283df87435809982a34117e
b71c75ee5174f7db94d04eccd4f12d

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 6a1ae4c2b1e7d4de0938f0bbd3392a6e94743c2f670c41a842dc016940cc3085
skS: 3f41102a583da027edb49986631de1a6bc904dba6d033e1181dedf318e5207d9
skE: 4696e8aedbb89088f9e7b494d65c79bfe2fc8beb51d978175e926d19654b8bfa
pkR: 1105499a2071ec0038a247e8f28fed721e358567ded31b60812692996a208841
pkS: c2c8706d3572f082e87bc3d2e0d4f315792ecb1c42f07b3286401f48e6b7dc09
pkE: dd2a4005e732ef69a0e8a5e5d97cdeed16e421e035d8eabbc1f1defa0612d83a
enc: dd2a4005e732ef69a0e8a5e5d97cdeed16e421e035d8eabbc1f1defa0612d83a
zz: 2d0bdaf3e16592f0488fc8a4566baf76fddc8d75b32bef0d63e9b4ffa9b47eff
context: 002000010003025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: 5baff645b6881fb83b69238a866fcf96bc3a20b55a6edef73e39d1a5512c0942
key: f1c3b72c0058f42457ed188edd73a6b24df2cb5d2f97a81fb3fc12b9d07d8e34
nonce: 746dc11a220eb063e7e5d6e1
exporterSecret:
6b909bad762f2fea406fde104b64a7061ee6c25cb34dcdc41ea5465c1116123c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 746dc11a220eb063e7e5d6e1
ciphertext: e4f438f7d88efcb8968fdce56b0186874a4f93fc5011a761edc496cc3841
fcad97fa9f42cb0f958aad662ac589

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 746dc11a220eb063e7e5d6e0
ciphertext: 724431e9c58b8e591dca76d4318edeb609cadbb45c03464ed0002d8d3ecc
377044d76a440b8b0bc4284062ffca

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 746dc11a220eb063e7e5d6e3
ciphertext: 4872f37ee3b84d32a6e2c8f6ab09961bd0fd9ec18cd707abc311be1831bb
58560b0cfcc69394693c8dbed97d95

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 746dc11a220eb063e7e5d6e5
ciphertext: 3cf1c78104abdd38346a13af7a6c92ee5193bd2cb4da3be3515fa569be75
cccb8b4498cf1e2740ee6ed311c6e4

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 32
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 3e2138be0398cdcd189d27496e3b114ef92fda8dc48abffff8850396ae363216
skS: d8449ff9fb1f851cd333bfb3984c345126c58d80d83be75c7823bef74d139444
skE: 9931463299979a635488a66b9c3e232aad6435a00483bbff55e74d1593cebe76
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0389faa129237b8564f9054f53cabd1f591e6cbb36a9d11358749898d9d32936
pkS: be6594706260ba7dc55e231c071d31ef7bc20366794a04661f57c6f8a900ab41
pkE: 408619f455c305ff1f7b2b6873a8938e539504d03a9e598e4229c5ca45339f2d
enc: 408619f455c305ff1f7b2b6873a8938e539504d03a9e598e4229c5ca45339f2d
zz: 2b68530f65f89d1b1bb796c589b7cf9679a03bc9b17732deddb56fc208c70493
context: 00200001000303535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: 0dd8e48f1db77e7336b7bfede2e567634e10d2d77d0364281a82e253b786e2fa
key: 386f26fdb2e5613d6d32562f75a04d837a21953141202c686ae6ecda9a46b0a2
nonce: d856b205ca6eeb095ebec28c
exporterSecret:
8169565da433fd9fa8778246bf2a7b5d11e525b8ac4d577cd4277e87afa95886
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: d856b205ca6eeb095ebec28c
ciphertext: 1741c361860f593983ed62f3578d73c5307b53a5672adb5d02a2b20bf46b
b71592f5672ebe302b1b53676f2115

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: d856b205ca6eeb095ebec28d
ciphertext: 5a118eb9c1e9ecddc0cbe127468aeddc2f9ff0bbcd204172f01b13a134e6
09066fc8452382355773f48067c6c5

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: d856b205ca6eeb095ebec28e
ciphertext: dab7ef7c3a8e709cc8fa6e69768d9725a17a62a2ebab30a27a172207c4a0
4181b446a237fe67eafa50a176a81d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: d856b205ca6eeb095ebec288
ciphertext: 86e185aa41a18008838453d8c6d7febfdfebeff91a7bf8186c55b92ab6a2
e6ca6684b829b763be66d1b90fb94c

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, AES-GCM-128

### Base Setup Information
~~~
mode: 0
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: ff49d8a732e028725d4c79bc07e36b766c22d22b2f0c216246af4c91b9735263
skE: b931cb5cc947cf7bb123d49ee06cccb728b7b0c728b5acc3198718bece464579
pkR: 04dc2f36df6caa9c66fba903fa3633019c6152e919085d523c0936d0557a95a70e1
d0bcbfcb8ba682fc0e69440e3b17accfd8256c708de0734386a910822be3640
pkE: 04711c163fd470d043213582c980336dd9e710b21d1596579397ca525dbb78e4f51
048d885a6e0e40cddeab9f81e5c84585c9b2b3c8446258f9d843cbc518f07e9
enc: 04711c163fd470d043213582c980336dd9e710b21d1596579397ca525dbb78e4f51
048d885a6e0e40cddeab9f81e5c84585c9b2b3c8446258f9d843cbc518f07e9
zz: 257a5fe87bce5f014be928503ba1320242971635307a4fe20745d21774341c66
context: 001000010001005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: 79a668637887c8acf90895d519740708b8dfd44f09be206d9d01694899e34a57
key: 3ca5026b27e79bf5ba0c28055205a4e8
nonce: 35cdbbddfde1ccc866da0920
exporterSecret:
7e30c84e0a1c3f47496be49adfc5eab1abe83d5955c72a9aced836f6744dcfb6
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 35cdbbddfde1ccc866da0920
ciphertext: dff64981d5f95fd63cc95f43c197da724f7e76208434c2744932b1171197
d64b3d8f4b461628b231d46f25f981

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 35cdbbddfde1ccc866da0921
ciphertext: fb27d31cc800babe2d316e03e0c14cd5e3d7151ac63eb7ae2c3b09bef809
7c26d23f91763c689e56136572202d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 35cdbbddfde1ccc866da0922
ciphertext: 9616cb0aed6c7a490968745e3cc8f792ae409877c8962c37765ecdad5198
7b5a3a656c316d5de146d539b6a2c9

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 35cdbbddfde1ccc866da0924
ciphertext: cf752b7dbce9176d19fa64467851706708133c15fbd9b10a8aa726838844
873ba61d0af1ec882f826f7a9ef299

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 7eb8d87e2715aff392ef9e8f950bc2af8eb748bcf95afe625bae62f452d89f33
skE: 090fa7a5d748ebead2846c6bef307e5cd6d63fa02fbd7aa173de9c86750da988
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0469d997f8ae5f52d903272dda2b00d316d010fef702b0a3fb3d88b1cf703ca6f44
cac6470f674e1ed04847798d09eb84ecf7ae4b2bb2ce6a473d25f4d67582716
pkE: 0404cccad34d9d898fb39c2045c65fef095a3fa5886327096620c455ae09efc9d35
65e1f9e93adda1fff9d212cadd756c377e2bf0828fba5097f13545963e847bb
enc: 0404cccad34d9d898fb39c2045c65fef095a3fa5886327096620c455ae09efc9d35
65e1f9e93adda1fff9d212cadd756c377e2bf0828fba5097f13545963e847bb
zz: 65e32d54de85ed42a6993da04b5122b1dca1db7eccb541b0840eb554cf4c621e
context: 00100001000101535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: c2f744b2709520a9518fb4f01a5a0ea8892602df7a1d6696f1015b3acc86630a
key: 94c5d5ebe2732bb3e26aa5ef0badaaf6
nonce: ab0c0e809dbfcda198abaec8
exporterSecret:
c58c80343a73afee8faeacb592c5b690bef48a3c17dc3da626c111e0d25c4cfb
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ab0c0e809dbfcda198abaec8
ciphertext: a6f3fee1ba5a0f94e6549c7652f54f45226cee2347e0e223182762e24ff8
9a31a89b8a82559e7270aef84254df

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ab0c0e809dbfcda198abaec9
ciphertext: 597d985a83a0a04ae359ffeb51d8bbf566d14777d6ed4042062be0c532de
fc9d28fc449270903d6aa5a35a7caa

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ab0c0e809dbfcda198abaeca
ciphertext: 23705d1af455fca85fcf65c8575ac1d79b4dd1e317fd2280db7ab9d01d78
9a342a5a59cfa24f59aedc883c38e9

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ab0c0e809dbfcda198abaecc
ciphertext: 3a8289890a10e55780167732becf957641dc3715db0e8696af82d7fb769e
98d07a0e372a2566283cf5a7fec3a0

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: bb8108a3fbf64e1719728d59dff6e4a8d016e8341e4233424211bcb695aae548
skS: 7c5018cce752cc68f42e053160bd9565821ba1a53b41711e02de3348c5e11f31
skE: 27b58fed3b471838bceaacd076714801abb047302972d84dce16c0387e524372
pkR: 0463ed6db63f3a5d09fe994566f72f02c40a0b29aeb26535e0c9c58ba4d38167e92
16d2b7fce7622451a11ddb41390a833850b2299282cbdec51a1d5f2fdb11fac
pkS: 04e96f472079488b456bc68d584a400dc7dbff4badae0519783cf2e96ad34942fd5
1bdefa3f185cdfd6fb4257923bba5c0d0338c3c716e88b217bc1ef4ffd9f62f
pkE: 04bce2666dd3d6e9de79bab61291dfec807e47a227d0e757f1be74ef8239da90432
37a400df18278067d89b33c253c97071e282ed9b32105b3ffd8390b01906f11
enc: 04bce2666dd3d6e9de79bab61291dfec807e47a227d0e757f1be74ef8239da90432
37a400df18278067d89b33c253c97071e282ed9b32105b3ffd8390b01906f11
zz: 83452815bfc3f1d45fb8b1c6f73923ae3a73c786394e9f402327dbfe07ec0aa1
context: 001000010001025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: 3e73c6542b62b017708f263af75d2370bd7d4fb4bab309a1ed3248619d7375c3
key: 549a027f7596f012e533750deb0e2d18
nonce: 59894492bddc850368b3e145
exporterSecret:
534fafc3f95e5b34bd44ac4566f71b634133ad734bfcd02d4e8f21a3869594b9
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 59894492bddc850368b3e145
ciphertext: 2899b4d3ba0a55a07f319a8947c9388d0fe181cdb3bcf74d8713a47ef188
8920b1af94769d64f58e22074dd57f

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 59894492bddc850368b3e144
ciphertext: 456bbb03aaf951f08204259291c0194577047118d9a8f2879214fc255b1a
1fb5c03c215c5b73856d50330061a2

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 59894492bddc850368b3e147
ciphertext: 4475a864c80b439b53b533e24f8d65aa43a44e4762967b01a24770476651
266b019e6091b3cab8491365f79e7e

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 59894492bddc850368b3e141
ciphertext: 2758492b36d15d42bde6c4bae360d6758281a6f5282e9afc303fbaba0563
01ec244bdffc2468059bd3a0ce172f

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 16
kdfID: 1
aeadID: 1
info: 4f6465206f6e2061204772656369616e2055726e
skR: 7440cbb0fcff8db2a606f63fbe3b97728cea0f198720124cbebf81ef0947431f
skS: 9627f39cb6022d2c5881c4b3f8a0842c0c3729d1b1d8b67e5efa9fb66d0035ab
skE: 1a86e1b409021c31432c2cff0af36c5ca73bf3b18f4348340919c66b4bc490f5
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04c69653d7bd87c44bacbc9e87dc1ffa9426867042309489f81dc87110f70f1dd21
6323108b1f3292f32a34e0dc192e7c01219e83f62e8c1c9757c77f4b5a5cab1
pkS: 0486a9295cc8094c26ce4ae9718c69e437d626c74fce21f52595b60375369646b6f
98d4adf85977003b5d28d93269add5ddf4ea332290ca7af08176e63e20bd5d5
pkE: 047d1ea269b51325198f231cc1d32757d377a8280bad2abda59939cca7973849baa
31c190e99a09cd768c22ab0b6e272815937842447d8f79e27425b8b8232ee0b
enc: 047d1ea269b51325198f231cc1d32757d377a8280bad2abda59939cca7973849baa
31c190e99a09cd768c22ab0b6e272815937842447d8f79e27425b8b8232ee0b
zz: ae393584aec8d31fdefe8d0efebf5cdfa9504c37431d842fe057388608d9b614
context: 00100001000103535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: 68d555445c59dbb33665fe9714cec1b176bc006f009c3d171629ac9f952c1277
key: 0a90565a27617d81607b21268369b3dd
nonce: 1ed13fe468d337f8f4fa08ee
exporterSecret:
99340c6468bfc4ba853a3fb7541d7d2d1a915683d30b3cc4f0234fd75cb472ff
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 1ed13fe468d337f8f4fa08ee
ciphertext: 85123615abb98da2398fb387c063738f37f860b5be011b414ac114f854a2
f2adcb474b1f3521df5d2799ca0826

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 1ed13fe468d337f8f4fa08ef
ciphertext: 32046ae8dbf51b8540b0dcf90ef36c96601c94439de047aa94147d267415
dc773b8dafc9820daaf1b422996277

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 1ed13fe468d337f8f4fa08ec
ciphertext: a947870947377422d446323ce879d9e964540ac5abea4344c3294ad6bb4d
b8e4b6c8bd7cb691da6f064a77764e

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 1ed13fe468d337f8f4fa08ea
ciphertext: 9b04289b6491bdc415e124c7bd38c19e55e67eca1474205eda530211904b
b63cb69e52a53fdf1c14674ebe02fa

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: c6362fd772537e65336f4b3c10fd473fde7b2d41f24d09c243e769358d05ff03
skE: a6a29d29e1fbb4fef70759d610546ef4ac787820b475e4a2b7a2b70f7e348a92
pkR: 0402d7375420ccb4f6b4e7418d94ca06e050c0a18b65bcd16f3e358a6b326fb9149
1765c612262c1f2d9c0abc22179f49ffa30091ee1aa2926b5f326d761bb87b7
pkE: 0400d973fb1b89f1240467a8859200b1353773cab731738f8b0af56d34db6464ee1
129088c09fd62e61ba6bbb3790a6f6c4d2578228639ca3833feaac2e2f24881
enc: 0400d973fb1b89f1240467a8859200b1353773cab731738f8b0af56d34db6464ee1
129088c09fd62e61ba6bbb3790a6f6c4d2578228639ca3833feaac2e2f24881
zz: 45bac8b800fa8b09891b509866f16e503e73b739d40760c60ca591086643823a
context: 001000010003005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: 60ff310a5fe01ed2d39e8887c9f6212beb0ef8c435140ebea2e5a50bc211b2b6
key: 6591f2039a2d080bfd30b6628ee603137eb233569a918f40c70e8c0676d53619
nonce: 8f0d8e3a0549d782abf79118
exporterSecret:
1e7c40f276463073ef8914ecae7fc2d89e22f67960cf0384bb7c7141479dda17
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 8f0d8e3a0549d782abf79118
ciphertext: 1dc3ead4b5ff2114901b93f5fb91c6e7ba14646ace91c2e30dfd151513b1
84e5ea98d5864465715321b4e0c621

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 8f0d8e3a0549d782abf79119
ciphertext: a64d0c1001c6ace9ea54b9d952f1ff50e83fd6309df98b4624d7ece20507
102f259f9bbda348801cb56678d5dc

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 8f0d8e3a0549d782abf7911a
ciphertext: de55d4d9553db8bc4c3d85a37de56c346a51f98cee5120dce337c7d3508f
2769f2d303c12b14cbec9898709f52

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 8f0d8e3a0549d782abf7911c
ciphertext: 20a52f9b69d054ce6d72cbf2214fd37ea9119f0ae12e4bce22b8e6852feb
ec46feb88dc16fc7117ad6f97add98

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 48f79bec0dc5df0be7cf85029e47e3f63ec9f1127b1b79a757a25e709e8d4672
skE: bbb0d359b1c83dd5b283aa0d045ec7f83c41772e1076bf6851627cfa462b6050
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 04a99379f44eb2594b1c1703b7364516bcad5ca9d6b595f25689067e5b474081ee9
07b38d3ce18124e892cd392c92be0e646ead7ec542867eedf4a6e8bf0905d08
pkE: 047e859e54498ff9684f1ebf5d6e5ed8a67c58d61c9c69b224c122b6a34a34ea03e
9fc98a96e48203a5d8bf156f1a9b4ae3b685bf101cf0b9cdd2d3161de03496c
enc: 047e859e54498ff9684f1ebf5d6e5ed8a67c58d61c9c69b224c122b6a34a34ea03e
9fc98a96e48203a5d8bf156f1a9b4ae3b685bf101cf0b9cdd2d3161de03496c
zz: fd9a9f8048d351468ac0b7fc2ee5eb817b66e17d66d4ba0691253acc7f9febf5
context: 00100001000301535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: 7417fb6ef11c081837378ff3a97f9da3d2ff252ab6624fcc93f3f3a423fd6cef
key: 2da95c89d6dec6977a49fa7139f5e80923bccdf54addc47dc5eb17033e8b8bf2
nonce: e4d01b9eca560895241a5718
exporterSecret:
578a5bacb193fd9219827d1012ab8e1f02d4e8f6cccfaa826279735251e62dbb
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: e4d01b9eca560895241a5718
ciphertext: 4092d9eb9f44451baaeade63f67ab95e5c238222ab7538dbd94e9e17004d
2e11101b7d55fdbf40fd8bebb9e8cd

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: e4d01b9eca560895241a5719
ciphertext: cd6dd628ac76f793dbcfc738edd97788b7959c061c5aa1cc348a73bb52ee
7f5ca15fe69f8bf41ffd26dd1c240b

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: e4d01b9eca560895241a571a
ciphertext: 9faff9d12778bb69ac388c12e258962bcdd907c57da5a46e3cf4350aec61
a420823587c4efba1fe72113987269

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: e4d01b9eca560895241a571c
ciphertext: a5e4e25fade1708a6968f0673a8dfeb18e1a572575a0a8eb4c84040cc728
212a8466f4aeda0c89a2fd346f0f23

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: d6af62908ce4f649422ff69d753398a6342b7a338d0e2e78ba1283077ecf4ff2
skS: bc2d7ae1d3a32e8fbf8592c1324a710143155168b634a2ac6bd86c716deb10ae
skE: 6a29aede8b323f7e1b266ff968eeb417c01daff9ae597f081be51e169667c27c
pkR: 04fdaa263df47a6ae59789b5864c7a0e530b9670dbb784197706b03011777549a08
17271c0cc40c3e26e1d0b12ac3fc5db9835b25c45309f54572eb309615fd766
pkS: 049abb3b012d0b6b119d5a06fda67cceca285586b829d5d32fb0f847d534ae161e9
651de0da04136df7f9a07a957a1f2a2de74d64f3fcb4714e4313de8c6c83f1e
pkE: 04e2524078c05f374484b5faaa2a05dbaa3d5825b3dd9dc97e2ae83cb28e97fcf9c
3bcf764b12c11adfdd1c1bb9dd518aa1c585862a2be6ee7c3d2cafb00bd8291
enc: 04e2524078c05f374484b5faaa2a05dbaa3d5825b3dd9dc97e2ae83cb28e97fcf9c
3bcf764b12c11adfdd1c1bb9dd518aa1c585862a2be6ee7c3d2cafb00bd8291
zz: 4db351faad5a4d247008902f52be4cd6b9c35fc3bf5867633a63b6cdd7e31bcc
context: 001000010003025d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570
cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: 347c5bd561ca6ed73b6f18383d93f8e60689720e5fe4175d1315e8bcfb2f9e1f
key: 6b9a0026045f7c8ad2d527740f8ff4ba9b607395701ab94ad005759e6e459229
nonce: 1d0ed4544cd50e0e47b68f81
exporterSecret:
01c22555dd3d90e8bb91f25b8cf1c4ba771e454d4c7c9ef7ecca5faa4e50aee9
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 1d0ed4544cd50e0e47b68f81
ciphertext: fc3cb87e1f7a42433b324489e0fb9ccf6ec76d9b557098108083a9878312
9a27a2bdbbbdfe04a9a97a703ed87e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 1d0ed4544cd50e0e47b68f80
ciphertext: 9157c4728a2c38cf482f6090887e5a1cc224216703a509ed5c364cef2bc9
cfb205071339a35dc7b68c110acd42

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 1d0ed4544cd50e0e47b68f83
ciphertext: 958efdc523d07a55247ab09c6f1ff25c6f27b2aa3ccd9b0682d557f0baef
57ebb103cdf0f0c9233c3bbb2cc405

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 1d0ed4544cd50e0e47b68f85
ciphertext: be2af428e2d9f1a2e8470f41c773847bf719d96551360b6b534a137b704e
152ee71535bebe654c9c24f2a40277

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 16
kdfID: 1
aeadID: 3
info: 4f6465206f6e2061204772656369616e2055726e
skR: 2f14b2c0024689bb498b260ed12835ca33fa805612b6f184e34b06d7cc24a640
skS: 9222b8822854c0db5461d030133d72bef55110e1a95090cfb61139b572a92a11
skE: 04e6915bdb7c58a00d83c58d567f9f8c0d89edc8d613246752564a481bca0c6a
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 043e66e114e1f5b391257fd9ad268bbac409a705e8bccba532cb92305d6fb052f3d
a7a4ba44877094e06eb114567b25dd3cb8418483ba74ac0f9a540f119d23636
pkS: 042ae6338f143580f41a88db10cb4b4be2d7020dd03807949eb6349e3541e1807d9
1827435844d90a4e4f22223aa0ea121000f92e220945e1155b1b4e5edd95133
pkE: 0463cb896d33ad5fd42b31746d46af3d2c1bf4669c43c10be1a278cd23597ac3a1d
72875e54fed873afee6fd522bf586968028da1b9b24c41cb522d64ef0574822
enc: 0463cb896d33ad5fd42b31746d46af3d2c1bf4669c43c10be1a278cd23597ac3a1d
72875e54fed873afee6fd522bf586968028da1b9b24c41cb522d64ef0574822
zz: b57ade8964feb031b79dea153420953cf3e6af9db78ee1db4211c325840c6dea
context: 00100001000303535aff74a3119261af116227072152ed4bb4de6308609d770
601639c3b7804bedebcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc5
24af4ce
secret: 72ccc2ef4a07b2a95f2b576f802dd1c0e87c3d83f663771841a2005e94ee2065
key: c8bc9c0d59f49eebc5a546557441521657852bb6f7708eb440b89de0c5d1f1a8
nonce: 7477605fd90857f5e641f850
exporterSecret:
91553b8f992e018e421445c7842cd265cc0cbe3dc28a75148a6ad609ec9d69d1
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 7477605fd90857f5e641f850
ciphertext: fceaf637789942a6cb21359ec34e1e0c4333cb0156879deac02b65c3adcc
c3d3956dae8a0542219dfacbd4fc84

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 7477605fd90857f5e641f851
ciphertext: c1420877f7eef569dc63d1f25b63f826bba19829d25f4444d27d4c4b6f95
b5667f43fa8bda8a1b82cadef7efea

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 7477605fd90857f5e641f852
ciphertext: eebd9d64de78ba6e1ba6480f7a6e7c31d47451358607ff1bba76304d14ae
bb545be2ccf397077f1a25f8f7d5dd

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 7477605fd90857f5e641f854
ciphertext: 8ef210ba8f00b248da7ecff13da26f672d63fa93245427005a111a29eb23
68444097614c2032fe2046cd481b72

~~~

## DHKEM(P-521, HKDF-SHA512), HKDF-SHA512, AES-GCM-256

### Base Setup Information
~~~
mode: 0
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 00018855ec92f0084fa06819deb1a53e53a87e4c691415744a846430d08b34a984b
faa6057070133ade23c26d5983f7c70edb47019376d0d1857912ff374271554e1
skE: 00512b511058e487593c85542982bb3660b63e9c26684f9693bc71d06b2ec700588
d58644cfef37da8ba698258bb50c4abadc6efbd40bbc4886c6fd17d02c8dd36a0
pkR: 0401d7d6cccecb0a859055f6c194bc384d9cd335a3cec4a40f23964060e61cc39d0
4537d2f2f352fa85a21cc1b69cd660b883891a2c2467cfd76cd0165e934befca9cb0167f
c2eeed0766bd6d3d356137e2e76d9d42e658a2e34a299caf8916258f53e38df1882a16b0
43caa826485e25806a5ba78b89393077467593c8ee7586456071d56
pkE: 040184de25d379296ff9eb72a54daafb83ae90b07d05646b4b800fb2e7d560c6a6a
26ee896d81bfbd8299c718bcddc3000ec5325be689307439451f695a8c8f58a697301dca
1273e05ce06703c47923a189bef45a61d453b50d8f9ec39b5de02b365a9d6c8a806e465c
991ed465c347b0fb1c7a0c1bf3f2397a97d30ce1ef6427473546cb3
enc: 040184de25d379296ff9eb72a54daafb83ae90b07d05646b4b800fb2e7d560c6a6a
26ee896d81bfbd8299c718bcddc3000ec5325be689307439451f695a8c8f58a697301dca
1273e05ce06703c47923a189bef45a61d453b50d8f9ec39b5de02b365a9d6c8a806e465c
991ed465c347b0fb1c7a0c1bf3f2397a97d30ce1ef6427473546cb3
zz: 3ebe874334686cc57b18578deae6d47938dd563b20af535d9317b392db0c2be49c2d
85809a5e0cba28edea1def782366e504ba36504f72c8f3de5c13dca9b47ccbff
context: 001200030002008ca13b5d680259cfa265de13dd24f257083c9403c01a8aa33
20b9195c8d1d812a58e72ff3dd3cf71dc81b21c354f84e9ca6863d5fd871711e356ed9bf
5f1e0d0c70a83df9dcea90e894cbfd709dabe93b3390a8e9c5a18498a1ff32414767a12c
08bf4d4df6cf9d953da725b79d07454eb69bd002235f35a241dec5f1088177c
secret: 54fbcd0e1dc84a6867074a5de24dad3aa9d1c192815a6e026545932a74f6a66d
8f78f9c977e849e733f7eac72b185518cacd30b57848708947287a581b76a563
key: ed5398764a1eb9b866274c8cca32a7a1d5d65dc9e8eb493574dfd0fd3b059b6b
nonce: f14762051ab70705203190c8
exporterSecret: af681b514d026238c4ba98aa24811b28c28abd526c22c907612af1a7
2d9ae6b5b13657a26c1248c3b1518161c95ccb1da268ab5e07aa45b5679097c98ee95a1c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: f14762051ab70705203190c8
ciphertext: 3d7f54fc77e2c322554f9d9d22321ebe50a1bb173b783432dd1c256524d2
f8e0300af9512c8f735277844853b7

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: f14762051ab70705203190c9
ciphertext: 572c783d8e536be1610cf17cfda0e32f0da1ea1654a491c29919d05074b9
c3eaa440a3c2100805bbd73a950770

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: f14762051ab70705203190ca
ciphertext: 43dfcfb4ad73dbc7c8d76c696e0c5a9e5a78a79cab0c159c3516e2d94cf0
6c3304fd27de9be789cc5a87c2d6dd

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: f14762051ab70705203190cc
ciphertext: 188a1904684a5d704c06fa2e869cac5a51f863e8f0a096cc679eb8c7106e
7a7c0d069c4e799ef9451f11690207

~~~

### PSK Setup Information
~~~
mode: 1
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 019dde938051b39e55f62e00ccd356e1e2ef63522c21336f86eedaabd14fe2faf62
b1dad1686f1ca652dcd1eb50e227a49e86cb223842daa00fadb30871db8b9e5ee
skE: 01a2fdbf10eb905eb1deffa2d6e04ac9e8a853accd23218833a719c3d84245b967b
a5837dbad1d391075b554b5ff1d217c0291a1a9ec819323d5f6c2a3a0cda584c3
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 0401e62cef3a5e06f3fc42206a474278e115ea6f181745332e107236445e7223972
7bd476886a61625f13e2180110e7ed70cd99e921a29ce1b59f5179ac56784e25c24017c7
43e526437b64035f53538c2a9216b593b1bff20b43ab75616af146797b1ece06df5252a7
0604e86e312fd3830e51ca534cb765f518c8a7c2ae01d27be7505a4
pkE: 0401d4e2a44ec47d2454bbcf3054df6ccf99acb8aceae02d9f3ab64f5a34f41b26a
2ff17063c55ef8345741e58846db4de4691c45e5902fa924f8562b397c0389aa7a80037e
bd6dfbd97db14ee6e9482cca23f4517ea98a5bb0723ccd88b4e89ad383f586874e35e802
eeef0baaa1eda5355e83893664fb76436e3bc863dd9e4d1d5442a34
enc: 0401d4e2a44ec47d2454bbcf3054df6ccf99acb8aceae02d9f3ab64f5a34f41b26a
2ff17063c55ef8345741e58846db4de4691c45e5902fa924f8562b397c0389aa7a80037e
bd6dfbd97db14ee6e9482cca23f4517ea98a5bb0723ccd88b4e89ad383f586874e35e802
eeef0baaa1eda5355e83893664fb76436e3bc863dd9e4d1d5442a34
zz: c967d7215ada8eeaf8438799c2e6ceaa58f9646ea5d0a7e65018a0a464d2e7fe1e0d
8d940340a63ed36bf1a3f4fbcbb815afe91c0edc3543dfd0620b6b7f1d0c6087
context: 0012000300020119d7c2d36b1355543d8247391c51c377929151509971ce1c3
cda0abff3f82068d844d47d7ad9b8f30f64092000c86f54b4904f7c96b6f306e8d335154
d673d8dc70a83df9dcea90e894cbfd709dabe93b3390a8e9c5a18498a1ff32414767a12c
08bf4d4df6cf9d953da725b79d07454eb69bd002235f35a241dec5f1088177c
secret: 3b2fe5edc2bea38ce17e57607fff552ca6678c6fceb2d62252cc5533daf1dc9b
8db79df284851b78fd97cff0308db129aa68c762d1780c2accd925ef767050ab
key: cc21d8ed058110e6acfdeb1519aa5206195b2393fb174cfd288c3ffcc0359f73
nonce: 7d2d14732ad3a01eb0f93be4
exporterSecret: c64e9c211732248450e219e9981199e9c6ff8af9c569644c88b7d008
5cc8f81543ef1fcc36b9ab506d73bcb7db8e2d419901454d235fa070b63a26e2a4c9c31e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 7d2d14732ad3a01eb0f93be4
ciphertext: 4db99d59a14365846f5fd442ffd3861a50371f451a63b55b8d915b0f1266
a28d9b699d6d8d3d6e2ac3bd77a367

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 7d2d14732ad3a01eb0f93be5
ciphertext: 13c804b531a34e1f6708d34bfcc114394ca67cea2771f5acf812602823a6
71f57d4670b648cb375167e21a84ee

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 7d2d14732ad3a01eb0f93be6
ciphertext: 7b786d30b4d9e11810117742825db0f85a6f3c80bbc9d84ba06ec6a5cdfe
d79186dfae9c8eec90ff4b40d864a4

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 7d2d14732ad3a01eb0f93be0
ciphertext: 4341c848692df6b553ce89b8594a29366a97c2eaf8dfecb112ddb24a296b
d4d2037fea336afeeb44224d782142

~~~

### Auth Setup Information
~~~
mode: 2
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 009c6dc6ecb1d209fb6dfc1cc291c0e539ab8a4c29c0b01d859f078e61c49e75aea
8fe98dc2be65694c7943cac2d58148bd2ee941b3dbfddb034f0a8047403c1218b
skS: 0086c32ca82f1d71d2934a33b27a60c52ef275d037c72ca9b8401506b302f413578
0b66bd1b8a58267ced54a6a4cfa2a0569714f3b0cac0921935bfec0745fc41c4e
skE: 00943303e9ca3d5dab5bc3c692131b024aa84890d6b237014b722bf30ecbff9243d
d0b5fc433fadfe05d9b1ff03b323723df0bb560edd3cf5f5bfe46d2fa0252a58a
pkR: 0401f2df9375e8e970fd127dc6db36e78b341d0e9faa9762b16dfbe029caa3a3516
331c48ab90f4f794b111e8f9a4d7339832bda50e202ddabb9422bd74482d2c809c4016cc
28bd2dad6dae82848ff5c352983e3a9f00b097f4e81e685f3bb241f90df334db44177e35
35ecfef09855ccfabd7b974c515dd5cc15657fbeb9353b52dd8598b
pkS: 04005aba1c7c02b5048120a2d67b5adf39993c0081c77f208cb64f3c46883f44db0
4ddb5d6e6aa359a6cbe647aea686f0e1afb68852e59a7363467869679a1010f513500272
01b8bb96c648db6fea73009dd5b82a8726435de3c6c1c9046c6fbd3e470354e1d6ca74b1
a7b8d7d34c5314172d7b5e0eec08c795504cffdff9f42054dbc1083
pkE: 040065a699da12aa772a419aa7966719cd8a127c1ea61bf1b873ecce0f3e3c79cbe
2b10493ca39ca56504f3cd139f1d68673d01697663c8a14a8d0d532c1f853e9c0bc00173
fc85329ecf695e581f09933c5d6251e42924968854b76d0f7a28716089113bdabb2a472c
e4af3cf69d4de447dca70bbfe5fdec805398186d1f2c5897d85b7d2
enc: 040065a699da12aa772a419aa7966719cd8a127c1ea61bf1b873ecce0f3e3c79cbe
2b10493ca39ca56504f3cd139f1d68673d01697663c8a14a8d0d532c1f853e9c0bc00173
fc85329ecf695e581f09933c5d6251e42924968854b76d0f7a28716089113bdabb2a472c
e4af3cf69d4de447dca70bbfe5fdec805398186d1f2c5897d85b7d2
zz: 7b9fd606446a9fc136bcbbf690bded9b028dd994e869a5c1987e9465c5fbea1e26fa
03f9fa207441e0080c116bd8a2dce0bb648b8a803dfd84cf83a787bd5f66fa1e
context: 001200030002028ca13b5d680259cfa265de13dd24f257083c9403c01a8aa33
20b9195c8d1d812a58e72ff3dd3cf71dc81b21c354f84e9ca6863d5fd871711e356ed9bf
5f1e0d0c70a83df9dcea90e894cbfd709dabe93b3390a8e9c5a18498a1ff32414767a12c
08bf4d4df6cf9d953da725b79d07454eb69bd002235f35a241dec5f1088177c
secret: 9dc82d274dfd5558b943e3e85ca70824228299e9e1ca352441f75d58eefc68cc
5b95a87cef0c94890e095f97f961608c1c1ffa7741a3f15d726bef162b0fd7a0
key: b7435104b86e2f8847d328e039428c6872a6b493cdfe9dd10f7a1df151f4be7b
nonce: 116ce075f803b49fc70bc302
exporterSecret: 66bca8b5786b7ff2e85eec035a6703a423d652df5c3ffd77d39e859e
7966fd2676d11469af6d6ca0292eaaa631db3e8471628e5b448de93f9df1a20c0c047277
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 116ce075f803b49fc70bc302
ciphertext: a957b8838f2ad96f7a88c3a9564fd26ea7c9711efa6fb30deb29852b60d8
fa0018dc12ae3f6ae50d8c55bf8bdc

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 116ce075f803b49fc70bc303
ciphertext: 182c87874b882cd6e241ce06c6bf6902ecf8690f86ef9be375f2e4f16be2
f73f1d08f923583b06306e3317e676

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 116ce075f803b49fc70bc300
ciphertext: f1f97feb3a4f4722244d8473df4f7ccfb0d7ad4b23461992b1dc1d0dd461
d88345aeabdd35297e919a2fe12f88

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 116ce075f803b49fc70bc306
ciphertext: 8473a239cf5dbbff900e716bb51aca54c85ad9c8d611993a0045aa781153
90413f07b18a688d8848269ab9eec5

~~~

### AuthPSK Setup Information
~~~
mode: 3
kemID: 18
kdfID: 3
aeadID: 2
info: 4f6465206f6e2061204772656369616e2055726e
skR: 007de2a76447a9d48343f83f163a5c8622dc6e3dc31c1e8a3ec5c6b5b0c8d8201c3
3d0b2903d75e2fbff4353fa42720eb45001c8009b08383c87e5389dd631719fa0
skS: 00c260caf4f5987cc0ed4de27f6b85e496622636e813d5b94e55a0f7d75edaffaf1
66f15ac7e18cf2fa37a7cc9b48a1bdc787e8341c3973281504b3eff44c81d700b
skE: 00218404c56690ca83f901a5812b7a50c878a8f1d9a148696947c00788b63e6196a
1bb816e4526d7baad6d0eb1d9c1a8d792362ab243c4c720296bfa8e23f2ee2e5a
psk: 5db3b80a81cb63ca59470c83414ef70a
pskID: 456e6e796e20447572696e206172616e204d6f726961
pkR: 040125de8d1b494a8040662e3130b85d0a36a459b3bbce16ed4a539630c558954e3
bf351c930bc253cd321d5dd59ff0ffe475a61f91c6ba37c9cbbcf19f4941808720f00825
824d46714299f1cef39632b238ab5d59aad804dfb2072702e8fa55930fb7ec722449e491
5bf8cc208f9d2a642d1d498fc39d83daed87492e147155e1c2fe03a
pkS: 04000fd8ffea534c0d88357932775a6b78afc82f692d62f583df9708778170f5e47
0da0b93c225b878c406171dcb96a6bd2429bb11edde5b4c0ab3b447c81c6becfd0e01eeb
db73ecf6f3d20e6ade2c7eb4d48069f1aa2a06294672cbb7c7198141db0c4bc81f726241
ae33b9b5f42be527c6284784bda1f8d3a2038c6ee783d69b329dd02
pkE: 040191f3d4126ad13095c4b526054b00ef82a29e3531d9ad7c54aa22335e7543dc4
94c85cd914688513a144c09a78cf4f8d49c54871d1be25e8d85b732b43c89eda523012eb
2ec28db8844537560d3f7bd20e7a17f244e18d7110cf4c872046ae29a0a98114e348f1bc
2c37779e54b2a860ded3f9037aa07b0ecb8ffc5d25d26bebb9cf714
enc: 040191f3d4126ad13095c4b526054b00ef82a29e3531d9ad7c54aa22335e7543dc4
94c85cd914688513a144c09a78cf4f8d49c54871d1be25e8d85b732b43c89eda523012eb
2ec28db8844537560d3f7bd20e7a17f244e18d7110cf4c872046ae29a0a98114e348f1bc
2c37779e54b2a860ded3f9037aa07b0ecb8ffc5d25d26bebb9cf714
zz: b6a933b3ee8040fe22e8ac93a86209ca84a87fbbeda19923c77b74ed6cfd077a5685
d82b77a804f556e902f9b628d4bc374ef4cbb81c8cb39c91525638c765c2b24e
context: 0012000300020319d7c2d36b1355543d8247391c51c377929151509971ce1c3
cda0abff3f82068d844d47d7ad9b8f30f64092000c86f54b4904f7c96b6f306e8d335154
d673d8dc70a83df9dcea90e894cbfd709dabe93b3390a8e9c5a18498a1ff32414767a12c
08bf4d4df6cf9d953da725b79d07454eb69bd002235f35a241dec5f1088177c
secret: 79d3f1e894eb52e46924bdbace168bcffcf50b72437ce04118b04bddc636327a
a3ed02ce434192a778d0e051c595c820ad928af6928477a62cdc64edfb5c4b40
key: 1da8c4af58055646fb2d38727e112b2976f2d9e97a7e307c55621837028bb1e2
nonce: a89332beb0a26fe353a8acbb
exporterSecret: 0dc3f1e98eb4085f2d8d858c6ef04b2355845989d02e3b6d2174112d
14f02bd53683bbb2bb2010d5f9f336c622de22f8f19e7bfaf869e107b9cb037ad85e5cea
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: a89332beb0a26fe353a8acbb
ciphertext: 50c233bc8fe4defcf4374e9e4a304a368cd5ad65f9c088e1a305f33471eb
a9d3d8e0d483d9b1d86b6d4b637f48

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: a89332beb0a26fe353a8acba
ciphertext: 2979c8209aef83ee83a6f787c970043766addfc0c95ccac4b8d63a8556f6
f21aa3bff742b1e8c07c78c5ebb17c

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: a89332beb0a26fe353a8acb9
ciphertext: 7ab40cd0b2e3d358175185b94bb3909f9db9577f4373d28e127585ee4e5b
9bf48879ef2706cf2cda09a171681b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: a89332beb0a26fe353a8acbf
ciphertext: 9680e17b6d180b9ef49a388ba6f345b06fbc5c9868043f63d612949241b6
5caf4b5a71e9f839fc9043e6b51276

~~~

