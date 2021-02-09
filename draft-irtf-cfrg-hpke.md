---
title: Hybrid Public Key Encryption
abbrev: HPKE
docname: draft-irtf-cfrg-hpke-latest
date:
category: info
workgroup: Internet Research Task Force (IRTF)

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
 -  ins: B. Lipp
    name: Benjamin Lipp
    org: Inria
    email: ietf@benjaminlipp.de
 -  ins: C. A. Wood
    name: Christopher A. Wood
    org: Cloudflare
    email: caw@heapingbits.net

informative:
  CS01:
    title: "Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack"
    target: https://eprint.iacr.org/2001/108
    date: 2001
    author:
      -
        ins: R. Cramer
        name: Ronald Cramer
      -
        ins: V. Shoup
        name: Victor Shoup

  HHK06:
    title: "Some (in)sufficient conditions for secure hybrid encryption"
    target: https://eprint.iacr.org/2006/265
    date: 2006
    author:
      -
        ins: J. Herranz
        name: Javier Herranz
      -
        ins: D. Hofheinz
        name: Dennis Hofheinz
      -
        ins: E. Kiltz
        name: Eike Kiltz

  GAP:
    title: "The Gap-Problems - a New Class of Problems for the Security of Cryptographic Schemes"
    target: https://link.springer.com/content/pdf/10.1007/3-540-44586-2_8.pdf
    date: 2001
    author:
      -
        ins: T. Okamoto
        name: Tatsuaki Okamoto
      -
        ins: D. Pointcheval
        name: David Pointcheval
    seriesinfo:
      ISBN: 978-3-540-44586-9

  ANSI:
    title: "ANSI X9.63 Public Key Cryptography for the Financial Services Industry -- Key Agreement and Key Transport Using Elliptic Curve Cryptography"
    date: 2001
    author:
      -
        ins:
        org: American National Standards Institute

  IEEE1363:
    title: IEEE 1363a, Standard Specifications for Public Key Cryptography - Amendment 1 -- Additional Techniques"
    date: 2004
    author:
      -
        ins:
        org: Institute of Electrical and Electronics Engineers

  ISO:
    title: "ISO/IEC 18033-2, Information Technology - Security Techniques - Encryption Algorithms - Part 2 -- Asymmetric Ciphers"
    date: 2006
    author:
      -
        ins:
        org: International Organization for Standardization / International Electrotechnical Commission

  SECG:
    title: "Elliptic Curve Cryptography, Standards for Efficient Cryptography Group, ver. 2"
    target: https://secg.org/sec1-v2.pdf
    date: 2009

  BHK09:
    title: "Subtleties in the Definition of IND-CCA: When and How Should Challenge-Decryption be Disallowed?"
    target: https://eprint.iacr.org/2009/418
    date: 2009
    author:
      -
        ins: Mihir Bellare
        org: University of California San Diego
      -
        ins: Dennis Hofheinz
        org: CWI Amsterdam
      -
        ins: Eike Kiltz
        org: CWI Amsterdam

  SigncryptionDZ10: DOI.10.1007/978-3-540-89411-7

  HPKEAnalysis:
    title: "An Analysis of Hybrid Public Key Encryption"
    target: https://eprint.iacr.org/2020/243.pdf
    date: 2020
    author:
      -
        ins: B. Lipp
        name: Benjamin Lipp
        org: Inria Paris

  ABHKLR20:
    title: "Analysing the HPKE Standard"
    target: https://eprint.iacr.org/2020/1499
    date: 2020
    author:
      -
        ins: J. Alwen
        name: Joël Alwen
        org: Wickr
      -
        ins: B. Blanchet
        name: Bruno Blanchet
        org: Inria Paris
      -
        ins: E. Hauck
        name: Eduard Hauck
        org: Ruhr-Universität Bochum
      -
        ins: E. Kiltz
        name: Eike Kiltz
        org: Ruhr-Universität Bochum
      -
        ins: B. Lipp
        name: Benjamin Lipp
        org: Inria Paris
      -
        ins: D. Riepel
        name: Doreen Riepel
        org: Ruhr-Universität Bochum

  MAEA10:
    title: "A Comparison of the Standardized Versions of ECIES"
    target: https://ieeexplore.ieee.org/abstract/document/5604194/
    date: 2010
    author:
      -
        ins: V. Gayoso Martinez
        name: V. Gayoso Martinez
        org: Applied Physics Institute, CSIC, Madrid, Spain
      -
        ins: F. Hernandez Alvarez
        name: F. Hernandez Alvarez
        org: Applied Physics Institute, CSIC, Madrid, Spain
      -
        ins: L. Hernandez Encinas
        name: L. Hernandez Encinas
        org: Applied Physics Institute, CSIC, Madrid, Spain
      -
        ins: C. Sanchez Avila
        name: C. Sanchez Avila
        org: Polytechnic University, Madrid, Spain

  BNT19:
    title: "Nonces Are Noticed: AEAD Revisited"
    target: http://dx.doi.org/10.1007/978-3-030-26948-7_9
    date: 2019
    author:
      -
        ins: M. Bellare
        name: Mihir Bellare
        org: University of California, San Diego
      -
        ins: R. Ng
        name: Ruth Ng
        org: University of California, San Diego
      -
        ins: B. Tackmann
        name: Björn Tackmann
        org: IBM Research

  IMB: DOI.10.1007/BF00124891

  LGR20:
    title: "Partitioning Oracle Attacks"
    date: To appear in USENIX Security 2021
    author:
      -
        ins: J. Len
        name: Julia Len
        org: Cornell Tech
      -
        ins: P. Grubbs
        name: Paul Grubbs
        org: Cornell Tech
      -
        ins: T. Ristenpart
        name: Thomas Ristenpart
        org: Cornell Tech

  TestVectors:
    title: "HPKE Test Vectors"
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/3d6ced124134825ed7a953b126cf5f756d960bc9/test-vectors.json
    date: 2020

  keyagreement: DOI.10.6028/NIST.SP.800-56Ar3

  NISTCurves: DOI.10.6028/NIST.FIPS.186-4

  GCM: DOI.10.6028/NIST.SP.800-38D

  WireGuard:
    title: "WireGuard: Next Generation Kernel Network Tunnel"
    target: https://www.wireguard.com/papers/wireguard.pdf
    date: 2020
    author:
      -
        ins: J. A. Donenfeld
        name: Jason A. Donenfeld

  NaCl:
    title: "Public-key authenticated encryption: crypto_box"
    target: https://nacl.cr.yp.to/box.html
    date: 2019

--- abstract

This document describes a scheme for hybrid public-key encryption
(HPKE).  This scheme provides authenticated public key encryption of
arbitrary-sized plaintexts for a recipient public key. HPKE works
for any combination of an asymmetric key encapsulation mechanism
(KEM), key derivation function (KDF), and authenticated encryption
with additional data (AEAD) encryption function. We provide
instantiations of the scheme using widely used and efficient
primitives, such as Elliptic Curve Diffie-Hellman key agreement,
HKDF, and SHA2.

This document is a product of the Crypto Forum Research Group (CFRG) in the IRTF.

--- middle

# Introduction

Encryption schemes that combine asymmetric and symmetric algorithms have been
specified and practiced since the early days of public-key cryptography, e.g.,
{{?RFC1421}}. Combining the two yields the key management advantages of asymmetric
cryptography and the performance benefits of symmetric cryptography. The traditional
combination has been "encrypt the symmetric key with the public key." "Hybrid"
public-key encryption schemes (HPKE), specified here, take a different approach:
"generate the symmetric key and its encapsulation with the public key."
Specifically, encrypted messages convey an encryption key encapsulated with a
public-key scheme, along with one or more arbitrary-sized ciphertexts encrypted
using that key. This type of public key encryption has many applications in
practice, including Messaging Layer Security {{?I-D.ietf-mls-protocol}} and
TLS Encrypted ClientHello {{?I-D.ietf-tls-esni}}.

Currently, there are numerous competing and non-interoperable standards and
variants for hybrid encryption, mostly based on ECIES, including ANSI X9.63
(ECIES) {{ANSI}}, IEEE 1363a {{IEEE1363}}, ISO/IEC 18033-2 {{ISO}}, and SECG SEC 1
{{SECG}}.  See {{MAEA10}} for a thorough comparison.  All these existing
schemes have problems, e.g., because they rely on outdated primitives, lack
proofs of IND-CCA2 security, or fail to provide test vectors.

This document defines an HPKE scheme that provides a subset
of the functions provided by the collection of schemes above, but
specified with sufficient clarity that they can be interoperably
implemented. The HPKE construction defined herein is secure against (adaptive)
chosen ciphertext attacks (IND-CCA2 secure) under classical assumptions about
the underlying primitives {{HPKEAnalysis}}, {{ABHKLR20}}. A summary of
these analyses is in {{sec-properties}}.

This document represents the consensus of the Crypto Forum Research Group (CFRG).

# Requirements Notation

{::boilerplate bcp14}

# Notation

The following terms are used throughout this document to describe the
operations, roles, and behaviors of HPKE:

- `(skX, pkX)`: A Key Encapsulation Mechanism (KEM) key pair used in role X,
  where X is one of S, R, or E as sender, receiver, and ephemeral, respectively;
  `skX` is the private key and `pkX` is the public key.
- `pk(skX)`: The KEM public key corresponding to the KEM private key `skX`.
- Sender (S): Role of entity which sends an encrypted message.
- Recipient (R): Role of entity which receives an encrypted message.
- Ephemeral (E): Role of a fresh random value meant for one-time use.
- `I2OSP(n, w)`: Convert non-negative integer `n` to a `w`-length,
  big-endian byte string as described in {{!RFC8017}}.
- `OS2IP(x)`: Convert byte string `x` to a non-negative integer as
  described in {{!RFC8017}}, assuming big-endian byte order.
- `concat(x0, ..., xN)`: Concatenation of byte strings.
  `concat(0x01, 0x0203, 0x040506) = 0x010203040506`.
- `random(n)`: A pseudorandom byte string of length `n` bytes
- `xor(a,b)`: XOR of byte strings; `xor(0xF0F0, 0x1234) = 0xE2C4`.
  It is an error to call this function with two arguments of unequal
  length.

# Cryptographic Dependencies {#base-crypto}

HPKE variants rely on the following primitives:

* A Key Encapsulation Mechanism (KEM):
  - `GenerateKeyPair()`: Randomized algorithm to generate a key pair `(skX, pkX)`.
  - `DeriveKeyPair(ikm)`: Deterministic algorithm to derive a key pair
    `(skX, pkX)` from the byte string `ikm`, where `ikm` SHOULD have at
    least `Nsk` bytes of entropy (see {{derive-key-pair}} for discussion).
  - `SerializePublicKey(pkX)`: Produce a byte string of length `Npk` encoding the
    public key `pkX`.
  - `DeserializePublicKey(pkXm)`: Parse a byte string of length `Npk` to recover a
    public key. This function can raise a `DeserializeError` error upon `pkXm`
    deserialization failure.
  - `Encap(pkR)`: Randomized algorithm to generate an ephemeral,
    fixed-length symmetric key (the KEM shared secret) and
    a fixed-length encapsulation of that key that can be decapsulated
    by the holder of the private key corresponding to `pkR`.
  - `Decap(enc, skR)`: Deterministic algorithm using the private key `skR`
    to recover the ephemeral symmetric key (the KEM shared secret) from
    its encapsulated representation `enc`. This function can raise an
    `DecapError` on decapsulation failure.
  - `AuthEncap(pkR, skS)` (optional): Same as `Encap()`, and the outputs
    encode an assurance that the KEM shared secret was generated by the
    holder of the private key `skS`.
  - `AuthDecap(enc, skR, pkS)` (optional): Same as `Decap()`, and the recipient
    is assured that the KEM shared secret was generated by the holder of
    the private key `skS`.
  - `Nsecret`: The length in bytes of a KEM shared secret produced by this KEM.
  - `Nenc`: The length in bytes of an encapsulated key produced by this KEM.
  - `Npk`: The length in bytes of an encoded public key for this KEM.
  - `Nsk`: The length in bytes of an encoded private key for this KEM.

* A Key Derivation Function (KDF):
  - `Extract(salt, ikm)`: Extract a pseudorandom key of fixed length `Nh` bytes
    from input keying material `ikm` and an optional byte string
    `salt`.
  - `Expand(prk, info, L)`: Expand a pseudorandom key `prk` using
    optional string `info` into `L` bytes of output keying material.
  - `Nh`: The output size of the `Extract()` function in bytes.

* An AEAD encryption algorithm {{!RFC5116}}:
  - `Seal(key, nonce, aad, pt)`: Encrypt and authenticate plaintext
    `pt` with associated data `aad` using symmetric key `key` and nonce
    `nonce`, yielding ciphertext and tag `ct`. This function
     can raise a `NonceOverflowError` upon failure.
  - `Open(key, nonce, aad, ct)`: Decrypt ciphertext and tag `ct` using
    associated data `aad` with symmetric key `key` and nonce `nonce`,
    returning plaintext message `pt`. This function can raise an
    `OpenError` or `NonceOverflowError` upon failure.
  - `Nk`: The length in bytes of a key for this algorithm.
  - `Nn`: The length in bytes of a nonce for this algorithm.

Beyond the above, a KEM MAY also expose the following functions, whose behavior
is detailed in {{serializeprivatekey}}:

- `SerializePrivateKey(skX)`: Produce a byte string of length `Nsk` encoding the private
  key `skX`.
- `DeserializePrivateKey(skXm)`: Parse a byte string of length `Nsk` to recover a
  private key. This function can raise a `DeserializeError` error upon `skXm`
  deserialization failure.

A _ciphersuite_ is a triple (KEM, KDF, AEAD) containing a choice of algorithm
for each primitive.

A set of algorithm identifiers for concrete instantiations of these
primitives is provided in {{ciphersuites}}.  Algorithm identifier
values are two bytes long.

Note that `GenerateKeyPair` can be implemented as `DeriveKeyPair(random(Nsk))`.

The notation `pk(skX)`, depending on its use and the KEM and its
implementation, is either the
computation of the public key using the private key, or just syntax
expressing the retrieval of the public key assuming it is stored along
with the private key object.

The following two functions are defined to facilitate domain separation of
KDF calls as well as context binding:

~~~
def LabeledExtract(salt, label, ikm):
  labeled_ikm = concat("HPKE-v1", suite_id, label, ikm)
  return Extract(salt, labeled_ikm)

def LabeledExpand(prk, label, info, L):
  labeled_info = concat(I2OSP(L, 2), "HPKE-v1", suite_id,
                        label, info)
  return Expand(prk, labeled_info, L)
~~~

The value of `suite_id` depends on where the KDF is used; it is assumed
implicit from the implementation and not passed as a parameter. If used
inside a KEM algorithm, `suite_id` MUST start with "KEM" and identify
this KEM algorithm; if used in the remainder of HPKE, it MUST start with
"HPKE" and identify the entire ciphersuite in use. See sections {{dhkem}}
and {{encryption-context}} for details.

## DH-Based KEM {#dhkem}

Suppose we are given a KDF, and a Diffie-Hellman group providing the
following operations:

- `DH(skX, pkY)`: Perform a non-interactive Diffie-Hellman exchange using
  the private key `skX` and public key `pkY` to produce a Diffie-Hellman shared secret of
  length `Ndh`. This function can raise a `ValidationError` as described
  in {{validation}}.
- `Ndh`: The length in bytes of a Diffie-Hellman shared secret produced
  by `DH()`.
- `Nsk`: The length in bytes of a Diffie-Hellman private key.

Then we can construct a KEM that implements the interface defined in {{base-crypto}}
called `DHKEM(Group, KDF)` in the following way, where `Group` denotes the
Diffie-Hellman group and `KDF` the KDF. The function parameters `pkR` and `pkS`
are deserialized public keys, and `enc` is a serialized public key. Since
encapsulated keys are Diffie-Hellman public keys in this KEM algorithm,
we use `SerializePublicKey()` and `DeserializePublicKey()` to encode and decode
them, respectively. `Npk` equals `Nenc`. `GenerateKeyPair()` produces a key pair
for the Diffie-Hellman group in use. {{derive-key-pair}} contains the
`DeriveKeyPair()` function specification for DHKEMs defined in this document.

~~~
def ExtractAndExpand(dh, kem_context):
  eae_prk = LabeledExtract("", "eae_prk", dh)
  shared_secret = LabeledExpand(eae_prk, "shared_secret",
                                kem_context, Nsecret)
  return shared_secret

def Encap(pkR):
  skE, pkE = GenerateKeyPair()
  dh = DH(skE, pkR)
  enc = SerializePublicKey(pkE)

  pkRm = SerializePublicKey(pkR)
  kem_context = concat(enc, pkRm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret, enc

def Decap(enc, skR):
  pkE = DeserializePublicKey(enc)
  dh = DH(skR, pkE)

  pkRm = SerializePublicKey(pk(skR))
  kem_context = concat(enc, pkRm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret

def AuthEncap(pkR, skS):
  skE, pkE = GenerateKeyPair()
  dh = concat(DH(skE, pkR), DH(skS, pkR))
  enc = SerializePublicKey(pkE)

  pkRm = SerializePublicKey(pkR)
  pkSm = SerializePublicKey(pk(skS))
  kem_context = concat(enc, pkRm, pkSm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret, enc

def AuthDecap(enc, skR, pkS):
  pkE = DeserializePublicKey(enc)
  dh = concat(DH(skR, pkE), DH(skR, pkS))

  pkRm = SerializePublicKey(pk(skR))
  pkSm = SerializePublicKey(pkS)
  kem_context = concat(enc, pkRm, pkSm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret
~~~

The implicit `suite_id` value used within `LabeledExtract` and
`LabeledExpand` is defined as follows, where `kem_id` is defined
in {{kem-ids}}:

~~~
suite_id = concat("KEM", I2OSP(kem_id, 2))
~~~

The KDF used in DHKEM can be equal to or different from the KDF used
in the remainder of HPKE, depending on the chosen variant.
Implementations MUST make sure to use the constants (`Nh`) and function
calls (`LabeledExtract`, `LabeledExpand`) of the appropriate KDF when
implementing DHKEM. See {{kdf-choice}} for a comment on the choice of
a KDF for the remainder of HPKE, and {{domain-separation}} for the
rationale of the labels.

For the variants of DHKEM defined in this document, the size `Nsecret` of the
KEM shared secret is equal to the output length of the hash function
underlying the KDF. For P-256, P-384 and P-521, the size `Ndh` of the
Diffie-Hellman shared secret is equal to 32, 48, and 66, respectively,
corresponding to the x-coordinate of the resulting elliptic curve point {{IEEE1363}}.
For X25519 and X448, the size `Ndh` of is equal to 32 and 56, respectively
(see {{?RFC7748}}, Section 5).

It is important to note that the `AuthEncap()` and `AuthDecap()` functions of the
DHKEM variants defined in this document are vulnerable to key-compromise
impersonation (KCI). This means the assurance that the KEM shared secret
was generated by the holder of the private key `skS` does not hold if
the recipient private key `skR` is compromised. See {{sec-properties}}
for more details.

Senders and recipients MUST validate KEM inputs and outputs as described
in {{kem-ids}}.

# Hybrid Public Key Encryption {#hpke}

In this section, we define a few HPKE variants.  All variants take a
recipient public key and a sequence of plaintexts `pt`, and produce an
encapsulated key `enc` and a sequence of ciphertexts `ct`.  These outputs are
constructed so that only the holder of `skR` can decapsulate the key from
`enc` and decrypt the ciphertexts.  All the algorithms also take an
`info` parameter that can be used to influence the generation of keys
(e.g., to fold in identity information) and an `aad` parameter that
provides Additional Authenticated Data to the AEAD algorithm in use.

In addition to the base case of encrypting to a public key, we
include three authenticated variants, one which authenticates
possession of a pre-shared key, one which authenticates
possession of a KEM private key, and one which authenticates possession of both
a pre-shared key and a KEM private key. All authenticated variants contribute
additional keying material to the encryption operation. The following one-byte
values will be used to distinguish between modes:

| Mode          | Value |
|:==============|:======|
| mode_base     | 0x00  |
| mode_psk      | 0x01  |
| mode_auth     | 0x02  |
| mode_auth_psk | 0x03  |
{: #hpke-modes title="HPKE Modes"}

All these cases follow the same basic two-step pattern:

1. Set up an encryption context that is shared between the sender
   and the recipient.
2. Use that context to encrypt or decrypt content.

A _context_ encodes the AEAD algorithm and key in use, and manages
the nonces used so that the same nonce is not used with multiple
plaintexts. It also has an interface for exporting secret values,
as described in {{hpke-export}}. See {{hpke-dem}} for a description
of this structure and its interfaces. HPKE decryption fails when
the underlying AEAD decryption fails.

The constructions described here presume that the relevant non-private
parameters (`enc`, `psk_id`, etc.) are transported between the sender and the
recipient by some application making use of HPKE. Moreover, a recipient with more
than one public key needs some way of determining which of its public keys was
used for the encapsulation operation. As an example, applications may send this
information alongside a ciphertext from sender to recipient. Specification of
such a mechanism is left to the application. See {{message-encoding}} for more
details.

Note that some KEMs may not support `AuthEncap()` or `AuthDecap()`.
For such KEMs, only `mode_base` or `mode_psk` are supported. Future specifications
which define new KEMs MUST indicate whether these modes are supported.
See {{future-kems}} for more details.

The procedures described in this session are laid out in a
Python-like pseudocode. The algorithms in use are left implicit.

## Creating the Encryption Context {#encryption-context}

The variants of HPKE defined in this document share a common
key schedule that translates the protocol inputs into an encryption
context. The key schedule inputs are as follows:

* `mode` - A one-byte value indicating the HPKE mode, defined in {{hpke-modes}}.
* `shared_secret` - A KEM shared secret generated for this transaction.
* `info` - Application-supplied information (optional; default value
  "").
* `psk` - A pre-shared key (PSK) held by both the sender
  and the recipient (optional; default value "").
* `psk_id` - An identifier for the PSK (optional; default value "").

Senders and recipients MUST validate KEM inputs and outputs as described
in {{kem-ids}}.

The `psk` and `psk_id` fields MUST appear together or not at all.
That is, if a non-default value is provided for one of them, then
the other MUST be set to a non-default value. This requirement is
encoded in `VerifyPSKInputs()` below.

The `psk`, `psk_id`, and `info` fields have maximum lengths that depend
on the KDF itself, on the definition of `LabeledExtract()`, and on the
constant labels used together with them. See {{kdf-input-length}} for
precise limits on these lengths.

The `key`, `base_nonce`, and `exporter_secret` computed by the key schedule
have the property that they are only known to the holder of the recipient
private key, and the entity that used the KEM to generate `shared_secret` and
`enc`.

In the Auth and AuthPSK modes, the recipient is assured that the sender
held the private key `skS`. This assurance is limited for the DHKEM
variants defined in this document because of key-compromise impersonation,
as described in {{dhkem}} and {{sec-properties}}. If in the PSK and
AuthPSK modes, the `psk` and `psk_id` arguments are provided as required,
then the recipient is assured that the sender held the corresponding
pre-shared key. See {{sec-properties}} for more details.

The HPKE algorithm identifiers, i.e., the KEM `kem_id`, KDF `kdf_id`, and
AEAD `aead_id` 2-byte code points as defined in {{kemid-values}}, {{kdfid-values}},
and {{aeadid-values}}, respectively, are assumed implicit from the implementation
and not passed as parameters. The implicit `suite_id` value used within
`LabeledExtract` and `LabeledExpand` is defined based on them as follows:

~~~
suite_id = concat(
  "HPKE",
  I2OSP(kem_id, 2),
  I2OSP(kdf_id, 2),
  I2OSP(aead_id, 2)
)
~~~

~~~~~
default_psk = ""
default_psk_id = ""

def VerifyPSKInputs(mode, psk, psk_id):
  got_psk = (psk != default_psk)
  got_psk_id = (psk_id != default_psk_id)
  if got_psk != got_psk_id:
    raise Exception("Inconsistent PSK inputs")

  if got_psk and (mode in [mode_base, mode_auth]):
    raise Exception("PSK input provided when not needed")
  if (not got_psk) and (mode in [mode_psk, mode_auth_psk]):
    raise Exception("Missing required PSK input")

def KeySchedule<ROLE>(mode, shared_secret, info, psk, psk_id):
  VerifyPSKInputs(mode, psk, psk_id)

  psk_id_hash = LabeledExtract("", "psk_id_hash", psk_id)
  info_hash = LabeledExtract("", "info_hash", info)
  key_schedule_context = concat(mode, psk_id_hash, info_hash)

  secret = LabeledExtract(shared_secret, "secret", psk)

  key = LabeledExpand(secret, "key", key_schedule_context, Nk)
  base_nonce = LabeledExpand(secret, "base_nonce",
                             key_schedule_context, Nn)
  exporter_secret = LabeledExpand(secret, "exp",
                                  key_schedule_context, Nh)

  return Context<ROLE>(key, base_nonce, 0, exporter_secret)
~~~~~

The `ROLE` template parameter is either S or R, depending on the role of
sender or recipient, respectively. See {{hpke-dem}} for a discussion of the
key schedule output, including the role-specific `Context` structure and its API.

Note that the `key_schedule_context` construction in `KeySchedule()` is
equivalent to serializing a structure of the following form in the TLS presentation
syntax:

~~~~~
struct {
    uint8 mode;
    opaque psk_id_hash[Nh];
    opaque info_hash[Nh];
} KeyScheduleContext;
~~~~~

### Encryption to a Public Key {#hpke-kem}

The most basic function of an HPKE scheme is to enable encryption
to the holder of a given KEM private key.  The `SetupBaseS()` and
`SetupBaseR()` procedures establish contexts that can be used to
encrypt and decrypt, respectively, for a given private key.

The KEM shared secret is combined via the KDF
with information describing the key exchange, as well as the
explicit `info` parameter provided by the caller.

The parameter `pkR` is a public key, and `enc` is an encapsulated
KEM shared secret.

~~~~~
def SetupBaseS(pkR, info):
  shared_secret, enc = Encap(pkR)
  return enc, KeyScheduleS(mode_base, shared_secret, info,
                           default_psk, default_psk_id)

def SetupBaseR(enc, skR, info):
  shared_secret = Decap(enc, skR)
  return KeyScheduleR(mode_base, shared_secret, info,
                      default_psk, default_psk_id)
~~~~~

### Authentication using a Pre-Shared Key {#mode-psk}

This variant extends the base mechanism by allowing the recipient to
authenticate that the sender possessed a given PSK. The PSK also
improves confidentiality guarantees in certain adversary models, as
described in more detail in {{sec-properties}}. We assume that both
parties have been provisioned with both the PSK value `psk` and another
byte string `psk_id` that is used to identify which PSK should be used.

The primary difference from the base case is that the `psk` and `psk_id` values
are used as `ikm` inputs to the KDF (instead of using the empty string).

The PSK MUST have at least 32 bytes of entropy and SHOULD be of length `Nh`
bytes or longer. See {{security-psk}} for a more detailed discussion.

~~~~~
def SetupPSKS(pkR, info, psk, psk_id):
  shared_secret, enc = Encap(pkR)
  return enc, KeyScheduleS(mode_psk, shared_secret, info, psk, psk_id)

def SetupPSKR(enc, skR, info, psk, psk_id):
  shared_secret = Decap(enc, skR)
  return KeyScheduleR(mode_psk, shared_secret, info, psk, psk_id)
~~~~~

### Authentication using an Asymmetric Key {#mode-auth}

This variant extends the base mechanism by allowing the recipient
to authenticate that the sender possessed a given KEM private key.
This assurance is based on the assumption that
`AuthDecap(enc, skR, pkS)` produces the correct KEM shared secret
only if the encapsulated value `enc` was produced by
`AuthEncap(pkR, skS)`, where `skS` is the private key corresponding
to `pkS`.  In other words, at most two entities (precisely two, in the case
of DHKEM) could have produced this secret, so if the recipient is at most one, then
the sender is the other with overwhelming probability.

The primary difference from the base case is that the calls to
`Encap()` and `Decap()` are replaced with calls to `AuthEncap()` and
`AuthDecap()`, which add the sender public key to their internal
context string. The function parameters `pkR` and `pkS` are
public keys, and `enc` is an encapsulated KEM shared secret.

Obviously, this variant can only be used with a KEM that provides
`AuthEncap()` and `AuthDecap()` procedures.

This mechanism authenticates only the key pair of the sender, not
any other identifier.  If an application wishes to bind HPKE
ciphertexts or exported secrets to another identity for the sender
(e.g., an email address or domain name), then this identifier should be
included in the `info` parameter to avoid identity mis-binding issues {{IMB}}.

~~~~~
def SetupAuthS(pkR, info, skS):
  shared_secret, enc = AuthEncap(pkR, skS)
  return enc, KeyScheduleS(mode_auth, shared_secret, info,
                           default_psk, default_psk_id)

def SetupAuthR(enc, skR, info, pkS):
  shared_secret = AuthDecap(enc, skR, pkS)
  return KeyScheduleR(mode_auth, shared_secret, info,
                      default_psk, default_psk_id)
~~~~~

### Authentication using both a PSK and an Asymmetric Key {#mode-auth-psk}

This mode is a straightforward combination of the PSK and
authenticated modes.  The PSK is passed through to the key schedule
as in the former, and as in the latter, we use the authenticated KEM
variants.

~~~~~
def SetupAuthPSKS(pkR, info, psk, psk_id, skS):
  shared_secret, enc = AuthEncap(pkR, skS)
  return enc, KeyScheduleS(mode_auth_psk, shared_secret, info,
                           psk, psk_id)

def SetupAuthPSKR(enc, skR, info, psk, psk_id, pkS):
  shared_secret = AuthDecap(enc, skR, pkS)
  return KeyScheduleR(mode_auth_psk, shared_secret, info,
                      psk, psk_id)
~~~~~

The PSK MUST have at least 32 bytes of entropy and SHOULD be of length `Nh`
bytes or longer. See {{security-psk}} for a more detailed discussion.

## Encryption and Decryption {#hpke-dem}

HPKE allows multiple encryption operations to be done based on a
given setup transaction.  Since the public-key operations involved
in setup are typically more expensive than symmetric encryption or
decryption, this allows applications to amortize the cost of the
public-key operations, reducing the overall overhead.

In order to avoid nonce reuse, however, this encryption must be
stateful. Each of the setup procedures above produces a role-specific
context object that stores the AEAD and Secret Export parameters.
The AEAD parameters consist of:

* The AEAD algorithm in use
* A secret `key`
* A base nonce `base_nonce`
* A sequence number (initially 0)

The Secret Export parameters consist of:

* The HPKE ciphersuite in use
* An `exporter_secret` used for the Secret Export interface; see {{hpke-export}}

All these parameters except the AEAD sequence number are constant.
The sequence number provides nonce uniqueness: The nonce used for
each encryption or decryption operation is the result of XORing
`base_nonce` with the current sequence number, encoded as a big-endian
integer of the same length as `base_nonce`. Implementations MAY use a
sequence number that is shorter than the nonce length (padding on the left
with zero), but MUST raise an error if the sequence number overflows.

Encryption is unidirectional from sender to recipient. The sender's
context can encrypt a plaintext `pt` with associated data `aad` as
follows:

~~~~~
def ContextS.Seal(aad, pt):
  ct = Seal(self.key, self.ComputeNonce(self.seq), aad, pt)
  self.IncrementSeq()
  return ct
~~~~~

The recipient's context can decrypt a ciphertext `ct` with associated
data `aad` as follows:

~~~~~
def ContextR.Open(aad, ct):
  pt = Open(self.key, self.ComputeNonce(self.seq), aad, ct)
  if pt == OpenError:
    raise OpenError
  self.IncrementSeq()
  return pt
~~~~~

Each encryption or decryption operation increments the sequence number for
the context in use. The per-message nonce and sequence number increment
details are as follows:

~~~~~
def Context<ROLE>.ComputeNonce(seq):
  seq_bytes = I2OSP(seq, Nn)
  return xor(self.base_nonce, seq_bytes)

def Context<ROLE>.IncrementSeq():
  if self.seq >= (1 << (8*Nn)) - 1:
    raise NonceOverflowError
  self.seq += 1
~~~~~

The sender's context MUST NOT be used for decryption. Similarly, the recipient's
context MUST NOT be used for encryption. Higher-level protocols re-using the HPKE
key exchange for more general purposes can derive separate keying material as
needed using use the Secret Export interface; see {{hpke-export}} and {{bidirectional}}
for more details.

It is up to the application to ensure that encryptions and decryptions are
done in the proper sequence, so that encryption and decryption nonces align.
If `ContextS.Seal()` or `ContextR.Open()` would cause the `seq` field to
overflow, then the implementation MUST fail with an error. (In the pseudocode
below, `Context<ROLE>.IncrementSeq()` fails with an error when `seq` overflows,
which causes `ContextS.Seal()` and `ContextR.Open()` to fail accordingly.)
Note that the internal `Seal()` and `Open()` calls inside correspond to the
context's AEAD algorithm.

## Secret Export {#hpke-export}

HPKE provides an interface for exporting secrets from the encryption context
using a variable-length PRF, similar to the TLS 1.3 exporter interface
(see {{?RFC8446}}, Section 7.5). This interface takes as input a context
string `exporter_context` and a desired length `L` in bytes, and produces
a secret derived from the internal exporter secret using the corresponding
KDF Expand function. For the KDFs defined in this specification, `L` has
a maximum value of `255*Nh`. Future specifications which define new KDFs
MUST specify a bound for `L`.

The `exporter_context` field has a maximum length that depends on the KDF
itself, on the definition of `LabeledExpand()`, and on the constant labels
used together with them. See {{kdf-input-length}} for precise limits on this
length.

~~~~~
def Context.Export(exporter_context, L):
  return LabeledExpand(self.exporter_secret, "sec",
                       exporter_context, L)
~~~~~

Applications that do not use the encryption API in {{hpke-dem}} can use
the export-only AEAD ID `0xFFFF` when computing the key schedule. Such
applications can avoid computing the `key` and `base_nonce` values in the
key schedule, as they are not used by the Export interface described above.

# Single-Shot APIs

## Encryption and Decryption {#single-shot-encryption}

In many cases, applications encrypt only a single message to a recipient's public key.
This section provides templates for HPKE APIs that implement stateless "single-shot"
encryption and decryption using APIs specified in {{hpke-kem}} and {{hpke-dem}}:

~~~~~
def Seal<MODE>(pkR, info, aad, pt, ...):
  enc, ctx = Setup<MODE>S(pkR, info, ...)
  ct = ctx.Seal(aad, pt)
  return enc, ct

def Open<MODE>(enc, skR, info, aad, ct, ...):
  ctx = Setup<MODE>R(enc, skR, info, ...)
  return ctx.Open(aad, ct)
~~~~~

The `MODE` template parameter is one of Base, PSK, Auth, or AuthPSK. The optional parameters
indicated by "..." depend on `MODE` and may be empty. `SetupBase()`, for example, has no
additional parameters. `SealAuthPSK()` and `OpenAuthPSK()` would be implemented as follows:

~~~
def SealAuthPSK(pkR, info, aad, pt, psk, psk_id, skS):
  enc, ctx = SetupAuthPSKS(pkR, info, psk, psk_id, skS)
  ct = ctx.Seal(aad, pt)
  return enc, ct

def OpenAuthPSK(enc, skR, info, aad, ct, psk, psk_id, pkS):
  ctx = SetupAuthPSKR(enc, skR, info, psk, psk_id, pkS)
  return ctx.Open(aad, ct)
~~~

## Secret Export

Applications may also want to derive a secret known only to a given recipient.
This section provides templates for HPKE APIs that implement stateless
"single-shot" secret export using APIs specified in {{hpke-export}}:

~~~
def SendExport<MODE>(pkR, info, exporter_context, L, ...):
  enc, ctx = Setup<MODE>S(pkR, info, ...)
  exported = ctx.Export(exporter_context, L)
  return enc, exported

def ReceiveExport<MODE>(enc, skR, info, exporter_context, L, ...):
  ctx = Setup<MODE>R(enc, skR, info, ...)
  return ctx.Export(exporter_context, L)
~~~

As in {{single-shot-encryption}}, the `MODE` template parameter is one of Base, PSK,
Auth, or AuthPSK. The optional parameters indicated by "..." depend on `MODE` and may
be empty.

# Algorithm Identifiers {#ciphersuites}

## Key Encapsulation Mechanisms (KEMs) {#kem-ids}

| Value  | KEM                        | Nsecret  | Nenc | Npk | Nsk | Auth | Reference                    |
|:-------|:---------------------------|:---------|:-----|:----|:----|:-----|:-----------------------------|
| 0x0000 | (reserved)                 | N/A      | N/A  | N/A | N/A | yes  | N/A                          |
| 0x0010 | DHKEM(P-256, HKDF-SHA256)  | 32       | 65   | 65  | 32  | yes  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0011 | DHKEM(P-384, HKDF-SHA384)  | 48       | 97   | 97  | 48  | yes  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0012 | DHKEM(P-521, HKDF-SHA512)  | 64       | 133  | 133 | 66  | yes  | {{NISTCurves}}, {{?RFC5869}} |
| 0x0020 | DHKEM(X25519, HKDF-SHA256) | 32       | 32   | 32  | 32  | yes  | {{?RFC7748}}, {{?RFC5869}}   |
| 0x0021 | DHKEM(X448, HKDF-SHA512)   | 64       | 56   | 56  | 56  | yes  | {{?RFC7748}}, {{?RFC5869}}   |
{: #kemid-values title="KEM IDs"}

The `Auth` column indicates if the KEM algorithm provides the `AuthEncap()`/`AuthDecap()`
interface. The meaning of all other columns is explained in {{kem-template}}.

### SerializePublicKey and DeserializePublicKey

For P-256, P-384 and P-521, the `SerializePublicKey()` function of the
KEM performs the uncompressed Elliptic-Curve-Point-to-Octet-String
conversion according to {{SECG}}. `DeserializePublicKey()` performs the
uncompressed Octet-String-to-Elliptic-Curve-Point conversion.

For X25519 and X448, the `SerializePublicKey()` and `DeserializePublicKey()`
functions are the identity function, since these curves already use
fixed-length byte strings for public keys.

Some deserialized public keys MUST be validated before they can be used. See
{{validation}} for specifics.

### SerializePrivateKey and DeserializePrivateKey {#serializeprivatekey}

As per {{SECG}}, P-256, P-384, and P-521 private keys are field elements in the
scalar field of the curve being used. For this section, and for
{{derive-key-pair}}, it is assumed that implementers of ECDH over these curves
use an integer representation of private keys that is compatible with the
`OS2IP()` function.

For P-256, P-384 and P-521, the `SerializePrivateKey()` function of the KEM
performs the Field-Element-to-Octet-String conversion according to {{SECG}}. If
the private key is an integer outside the range `[0, order-1]`, where `order`
is the order of the curve being used, the private key MUST be reduced to its
representative in `[0, order-1]` before being serialized.
`DeserializePrivateKey()` performs the Octet-String-to-Field-Element conversion
according to {{SECG}}.

For X25519 and X448, private keys are identical to their byte string
representation, so little processing has to be done. The
`SerializePrivateKey()` function MUST clamp its output and
`DeserializePrivateKey()` MUST clamp its input, where _clamping_ refers to the
bitwise operations performed on `k` in the `decodeScalar25519()` and
`decodeScalar448()` functions defined in section 5 of {{?RFC7748}}.

To catch invalid keys early on, implementers of DHKEMs SHOULD check that
deserialized private keys are not equivalent to 0 (mod `order`), where `order`
is the order of the DH group. Note that this property is trivially true for X25519
and X448 groups, since clamped values can never be 0 (mod `order`).

### DeriveKeyPair {#derive-key-pair}

The keys that `DeriveKeyPair()` produces have only as much entropy as the provided
input keying material. For a given KEM, the `ikm` parameter given to `DeriveKeyPair()` SHOULD
have length at least `Nsk`, and SHOULD have at least `Nsk` bytes of entropy.

All invocations of KDF functions (such as `LabeledExtract` or `LabeledExpand`) in any
DHKEM's `DeriveKeyPair()` function use the DHKEM's associated KDF (as opposed to
the ciphersuite's KDF).

For P-256, P-384 and P-521, the `DeriveKeyPair()` function of the KEM performs
rejection sampling over field elements:

~~~
def DeriveKeyPair(ikm):
  dkp_prk = LabeledExtract("", "dkp_prk", ikm)
  sk = 0
  counter = 0
  while sk == 0 or sk >= order:
    if counter > 255:
      raise DeriveKeyPairError
    bytes = LabeledExpand(dkp_prk, "candidate",
                          I2OSP(counter, 1), Nsk)
    bytes[0] = bytes[0] & bitmask
    sk = OS2IP(bytes)
    counter = counter + 1
  return (sk, pk(sk))
~~~

`order` is the order of the curve being used (see section D.1.2 of {{NISTCurves}}), and
is listed below for completeness.

~~~~~
P-256:
0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

P-384:
0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf
  581a0db248b0a77aecec196accc52973

P-521:
0x01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  fa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409
~~~~~

`bitmask` is defined to be 0xFF for P-256 and P-384, and 0x01 for P-521.
The precise likelihood of `DeriveKeyPair()` failing with DeriveKeyPairError
depends on the group being used, but it is negligibly small in all cases.

For X25519 and X448, the `DeriveKeyPair()` function applies a KDF to the input:

~~~
def DeriveKeyPair(ikm):
  dkp_prk = LabeledExtract("", "dkp_prk", ikm)
  sk = LabeledExpand(dkp_prk, "sk", "", Nsk)
  return (sk, pk(sk))
~~~

### Validation of Inputs and Outputs {#validation}

The following public keys are subject to validation if the group
requires public key validation: the sender MUST validate the recipient's
public key `pkR`; the recipient MUST validate the ephemeral public key
`pkE`; in authenticated modes, the recipient MUST validate the sender's
static public key `pkS`.

For P-256, P-384 and P-521, senders and recipients MUST perform partial
public-key validation on all public key inputs, as defined in section 5.6.2.3.4
of {{keyagreement}}. This includes checking that the coordinates are in the
correct range, that the point is on the curve, and that the point is not the
point at infinity. Additionally, senders and recipients MUST ensure the
Diffie-Hellman shared secret is not the point at infinity.

For X25519 and X448, public keys and Diffie-Hellman outputs MUST be validated
as described in {{?RFC7748}}. In particular, recipients MUST check whether
the Diffie-Hellman shared secret is the all-zero value and abort if so.

### Future KEMs {#future-kems}

{{kem-security}} lists security requirements on a KEM used within HPKE.

The `AuthEncap()` and `AuthDecap()` functions are OPTIONAL. If a KEM algorithm
does not provide them, only the Base and PSK modes of HPKE are supported.
Future specifications which define new KEMs MUST indicate whether or not
Auth and AuthPSK modes are supported.

A KEM algorithm may support different encoding algorithms, with different output
lengths, for KEM public keys. Such KEM algorithms MUST specify only one encoding
algorithm whose output length is `Npk`.

## Key Derivation Functions (KDFs) {#kdf-ids}

| Value  | KDF         | Nh  | Reference    |
|:-------|:------------|-----|:-------------|
| 0x0000 | (reserved)  | N/A | N/A          |
| 0x0001 | HKDF-SHA256 | 32  | {{?RFC5869}} |
| 0x0002 | HKDF-SHA384 | 48  | {{?RFC5869}} |
| 0x0003 | HKDF-SHA512 | 64  | {{?RFC5869}} |
{: #kdfid-values title="KDF IDs"}

### Input Length Restrictions {#kdf-input-length}

This document defines `LabeledExtract()` and `LabeledExpand()` based on the
KDFs listed above. These functions add prefixes to their respective
inputs `ikm` and `info` before calling the KDF's `Extract()` and `Expand()`
functions. This leads to a reduction of the maximum input length that
is available for the inputs `psk`, `psk_id`, `info`, `exporter_context`,
i.e., the variable-length parameters provided by HPKE applications.
The following table lists the maximum allowed lengths of these fields
for the KDFs defined in this document, as inclusive bounds in bytes:

| Input            | HKDF-SHA256  | HKDF-SHA384   | HKDF-SHA512   |
|:-----------------|:-------------|:--------------|:--------------|
| psk              | 2^{61} - 88  | 2^{125} - 152 | 2^{125} - 152 |
| psk_id           | 2^{61} - 93  | 2^{125} - 157 | 2^{125} - 157 |
| info             | 2^{61} - 91  | 2^{125} - 155 | 2^{125} - 155 |
| exporter_context | 2^{61} - 120 | 2^{125} - 200 | 2^{125} - 216 |
{: #input-limits title="Application Input Limits"}

This shows that the limits are only marginally smaller than the maximum
input length of the underlying hash function; these limits are large and
unlikely to be reached in practical applications. Future specifications
which define new KDFs MUST specify bounds for these variable-length
parameters.

The values for `psk`, `psk_id`, and `info` which are inputs to
`LabeledExtract()` were computed with the following expression:

~~~
max_size_hash_input - Nb - size_version_label -
    size_suite_id - size_input_label
~~~

The value for `exporter_context` which is an input to `LabeledExpand()`
was computed with the following expression:

~~~
max_size_hash_input - Nb - Nh - size_version_label -
    size_suite_id - size_input_label - 2 - 1
~~~

In these equations, `max_size_hash_input` is the maximum input length
of the underlying hash function in bytes, `Nb` is the block size of the
underlying hash function in bytes, `size_version_label` is the size
of "HPKE-v1" in bytes and equals 7, `size_suite_id` is the size of the
`suite_id` and equals 10, and `size_input_label` is the size
of the label used as parameter to `LabeledExtract()` or `LabeledExpand()`.

## Authenticated Encryption with Associated Data (AEAD) Functions {#aead-ids}

| Value  | AEAD             | Nk  | Nn  | Reference    |
|:-------|:-----------------|:----|:----|:-------------|
| 0x0000 | (reserved)       | N/A | N/A | N/A          |
| 0x0001 | AES-128-GCM      | 16  | 12  | {{GCM}}      |
| 0x0002 | AES-256-GCM      | 32  | 12  | {{GCM}}      |
| 0x0003 | ChaCha20Poly1305 | 32  | 12  | {{?RFC8439}} |
| 0xFFFF | Export-only      | N/A | N/A | [[RFCXXXX]]  |
{: #aeadid-values title="AEAD IDs"}

The `0xFFFF` AEAD ID is reserved for applications which only use the Export
interface; see {{hpke-export}} for more details.

# Security Considerations {#sec-considerations}

## Security Properties {#sec-properties}

HPKE has several security goals, depending on the mode of operation,
against active and adaptive attackers that can compromise partial
secrets of senders and recipients. The desired security goals are
detailed below:

* Message secrecy: Confidentiality of the sender's messages against
  chosen ciphertext attacks
* Export key secrecy: Indistinguishability of each export
  secret from a uniformly random bitstring of equal length, i.e.,
  `Context.Export` is a variable-length PRF
* Sender authentication: Proof of sender origin for PSK, Auth, and
  AuthPSK modes

These security goals are expected to hold for any honest sender and
honest recipient keys, as well as if the honest sender and honest
recipient keys are the same.

As noted in {{non-goals}}, HPKE does not provide forward secrecy.
In the Base and Auth modes, the secrecy properties are only expected to
hold if the recipient private key `skR` is not compromised at any point
in time. In the PSK and AuthPSK modes, the secrecy properties are
expected to hold if the recipient private key `skR` and the pre-shared key
are not both compromised at any point in time.

In the Auth mode, sender authentication is generally expected to hold if
the sender private key `skS` is not compromised at the time of message
reception. In the AuthPSK mode, sender authentication is generally
expected to hold if at the time of message reception, the sender private
key skS and the pre-shared key are not both compromised.

### Key-Compromise Impersonation

The DHKEM variants defined in this document are
vulnerable to key-compromise impersonation attacks {{?BJM97=DOI.10.1007/BFb0024447}},
which means that sender authentication cannot be expected to hold in the
Auth mode if the recipient private key `skR` is compromised, and in the
AuthPSK mode if the pre-shared key and the recipient private key `skR` are
both compromised. NaCl's `box` interface {{NaCl}} has the same issue. At
the same time, this enables repudiability.

As shown by {{ABHKLR20}}, key-compromise impersonation attacks are generally possible on HPKE
because KEM ciphertexts are not bound to HPKE messages. An adversary who
knows a recipient's private key can decapsulate an observed KEM ciphertext,
compute the key schedule, and encrypt an arbitrary message that the recipient
will accept as coming from the original sender. Importantly, this is possible even
with a KEM that is resistant to key-compromise impersonation attacks. As a
result, mitigating this issue requires fundamental changes that are out-of-scope
of this specification.

Applications that require resistance against key-compromise impersonation
SHOULD take extra steps to prevent this attack. One possibility is to
produce a digital signature over `(enc, ct)` tuples using a sender's
private key -- where `ct` is an AEAD ciphertext produced by the single-shot
or multi-shot API, and `enc` the corresponding KEM encapsulated key.

Given these properties, pre-shared keys strengthen both the authentication and the
secrecy properties in certain adversary models. One particular example in which
this can be useful is a hybrid quantum setting: if a
non-quantum-resistant KEM used with HPKE is broken by a
quantum computer, the security properties are preserved through the use
of a pre-shared key. This assumes that the pre-shared key has not been
compromised, as described in {{WireGuard}}.

### Computational Analysis

It is shown in {{CS01}} that a hybrid public-key encryption scheme of
essentially the same form as the Base mode described here is
IND-CCA2-secure as long as the underlying KEM and AEAD schemes are
IND-CCA2-secure. Moreover, it is shown in {{HHK06}} that IND-CCA2 security
of the KEM and the data encapsulation mechanism are necessary conditions
to achieve IND-CCA2 security for hybrid public-key encryption.
The main difference between the scheme proposed in {{CS01}}
and the Base mode in this document (both named HPKE) is that we interpose
some KDF calls between the KEM and the AEAD. Analyzing the HPKE Base mode
instantiation in this document therefore requires verifying that the
additional KDF calls do not cause the IND-CCA2 property to fail, as
well as verifying the additional export key secrecy property.

Analysis of the PSK, Auth, and AuthPSK modes defined in this document
additionally requires verifying the sender authentication property.
While the PSK mode just adds supplementary keying material to the key
schedule, the Auth and AuthPSK modes make use of a non-standard
authenticated KEM construction. Generally, the authenticated modes of
HPKE can be viewed and analyzed as flavors of signcryption {{SigncryptionDZ10}}.

A preliminary computational analysis of all HPKE modes has been done
in {{HPKEAnalysis}}, indicating asymptotic security for the case where
the KEM is DHKEM, the AEAD is any IND-CPA and INT-CTXT-secure scheme,
and the DH group and KDF satisfy the following conditions:

- DH group: The gap Diffie-Hellman (GDH) problem is hard in the
  appropriate subgroup {{GAP}}.
- `Extract()` and `Expand()` (in DHKEM): `Extract()` can be modeled as
  a random oracle. `Expand()` can be modeled as a pseudorandom function,
  wherein the first argument is the key.
- `Extract()` and `Expand()` (elsewhere): `Extract()` can be modeled as
  a random oracle. `Expand()` can be modeled as a pseudorandom function,
  wherein the first argument is the key.

In particular, the KDFs and DH groups defined in this document (see
{{kdf-ids}} and {{kem-ids}}) satisfy these properties when used as
specified. The analysis in {{HPKEAnalysis}} demonstrates that under these
constraints, HPKE continues to provide IND-CCA2 security, and provides
the additional properties noted above. Also, the analysis confirms the
expected properties hold under the different key compromise cases
mentioned above. The analysis considers a sender that sends one message
using the encryption context, and additionally exports two independent
secrets using the secret export interface.

The table below summarizes the main results from {{HPKEAnalysis}}. N/A
means that a property does not apply for the given mode, whereas `y` means
the given mode satisfies the property.

| Variant | Message Sec. | Export Sec. | Sender Auth. |
|:--------|:------------:|:-----------:|:------------:|
| Base    | y            | y           | N/A          |
| PSK     | y            | y           | y            |
| Auth    | y            | y           | y            |
| AuthPSK | y            | y           | y            |

If non-DH-based KEMs are to be used with HPKE, further analysis will be
necessary to prove their security. The results from {{CS01}} provide
some indication that any IND-CCA2-secure KEM will suffice here, but are
not conclusive given the differences in the schemes.

A detailed computational analysis of HPKE's Auth mode single-shot
encryption API has been done in {{ABHKLR20}}.
The paper defines security notions for authenticated
KEMs and for authenticated public key encryption, using the outsider and
insider security terminology known from signcryption {{SigncryptionDZ10}}.
The analysis proves that DHKEM's `AuthEncap()`/`AuthDecap()` interface
fulfills these notions for all Diffie-Hellman groups specified in this document,
and indicates exact security bounds, under the assumption that the
gap Diffie-Hellman (GDH) problem is hard in the appropriate subgroup {{GAP}},
and that HKDF can be modeled as a random oracle.

Further, {{ABHKLR20}} proves composition theorems, showing that HPKE's
Auth mode fulfills the security notions of authenticated public key encryption
for all KDFs and AEAD schemes specified in this document, given any
authenticated KEM satisfying the previously defined security notions
for authenticated KEMs. The assumptions on the KDF are that `Extract()`
and `Expand()` can be modeled as pseudorandom functions wherein the first
argument is the key, respectively. The assumption for the AEAD is
IND-CPA and IND-CTXT security.

In summary, the analysis in {{ABHKLR20}} proves that the single-shot encryption API of HPKE's
Auth mode satisfies the desired message confidentiality and sender
authentication properties listed at the beginning of this section;
it does not consider multiple messages, nor the secret export API.

### Post-Quantum Security

All of {{CS01}}, {{HPKEAnalysis}}, and {{ABHKLR20}} are premised on
classical security models and assumptions, and do not consider
adversaries capable of quantum computation. A full proof of post-quantum
security would need to take appropriate security models and assumptions
into account, in addition to simply using a post-quantum KEM. However,
the composition theorems from {{ABHKLR20}} for HPKE's Auth mode only make
standard assumptions (i.e., no random oracle assumption) that are expected
to hold against quantum adversaries (although with slightly worse bounds).
Thus, these composition theorems, in combination with a post-quantum-secure
authenticated KEM, guarantee the post-quantum security of HPKE's Auth mode.
In future work, the analysis from {{ABHKLR20}} can be extended to cover
HPKE's other modes and desired security properties.
The hybrid quantum-resistance property described above, which is achieved
by using the PSK or AuthPSK mode, is not proven in {{HPKEAnalysis}} because
this analysis requires the random oracle model; in a quantum
setting, this model needs adaption to, for example, the quantum random
oracle model.

## Security Requirements on a KEM used within HPKE {#kem-security}

A KEM used within HPKE MUST allow HPKE to satisfy its desired security
properties described in {{sec-properties}}. In particular, the KEM
shared secret MUST be a uniformly random byte string of length `Nsecret`.
This means, for instance, that it would not be sufficient if the KEM
shared secret is only uniformly random as an element of some set prior
to its encoding as byte string.

### Encap/Decap Interface

As mentioned in {{sec-considerations}}, {{CS01}} provides some indications
that if the KEM's `Encap()`/`Decap()` interface (which is used in the Base
and PSK modes), is IND-CCA2-secure, HPKE is able to satisfy its desired
security properties. An appropriate definition of IND-CCA2-security for
KEMs can be found in {{CS01}} and {{BHK09}}.

### AuthEncap/AuthDecap Interface

The analysis of HPKE's Auth mode single-shot encryption API in {{ABHKLR20}}
provides composition theorems that guarantee that HPKE's Auth mode achieves
its desired security properties if the KEM's `AuthEncap()`/`AuthDecap()`
interface satisfies multi-user Outsider-CCA, Outsider-Auth, and
Insider-CCA security as defined in the same paper.

Intuitively, Outsider-CCA security formalizes confidentiality, and
Outsider-Auth security formalizes authentication of the KEM shared secret
in case none of the sender or recipient private keys are compromised.
Insider-CCA security formalizes confidentiality of the KEM shared secret
in case the sender private key is known or chosen by the adversary.
(If the recipient private key is known or chosen by the adversary,
confidentiality is trivially broken, because then the adversary knows
all secrets on the recipient's side).

An Insider-Auth security notion would formalize authentication of the
KEM shared secret in case the recipient private key is known or chosen
by the adversary. (If the sender private key is known or chosen by the
adversary, it can create KEM ciphertexts in the name of the sender).
Because of the generic attack on an analogous Insider-Auth security
notion of HPKE described in {{sec-properties}}, a definition of
Insider-Auth security for KEMs used within HPKE is not useful.

## Security Requirements on a KDF {#kdf-choice}

The choice of the KDF for the remainder of HPKE SHOULD be made based on
the security level provided by the KEM and, if applicable, by the PSK.
The KDF SHOULD have at least have the security level of the KEM and
SHOULD at least have the security level provided by the PSK.

## Pre-Shared Key Recommendations {#security-psk}

In the PSK and AuthPSK modes, the PSK MUST have at least 32 bytes of
entropy and SHOULD be of length `Nh` bytes or longer. Using a PSK longer than
32 bytes but shorter than `Nh` bytes is permitted.

HPKE is specified to use HKDF as key derivation function. HKDF is not
designed to slow down dictionary attacks, see {{?RFC5869}}. Thus, HPKE's
PSK mechanism is not suitable for use with a low-entropy password as the
PSK: in scenarios in which the adversary knows the KEM shared secret
`shared_secret` and has access to an oracle that allows to distinguish between
a good and a wrong PSK, it can perform PSK-recovering attacks. This oracle
can be the decryption operation on a captured HPKE ciphertext or any other
recipient behavior which is observably different when using a wrong PSK.
The adversary knows the KEM shared secret `shared_secret` if it knows all
KEM private keys of one participant. In the PSK mode this is trivially
the case if the adversary acts as sender.

To recover a lower entropy PSK, an attacker in this scenario can trivially
perform a dictionary attack. Given a set `S` of possible PSK values, the
attacker generates an HPKE ciphertext for each value in `S`, and submits
the resulting ciphertexts to the oracle to learn which PSK is being used by
the recipient. Further, because HPKE uses AEAD schemes that are not key-committing,
an attacker can mount a partitioning oracle attack {{LGR20}} which can recover
the PSK from a set of `S` possible PSK values, with |S| = m\*k, in roughly
m + log k queries to the oracle using ciphertexts of length proportional to
k, the maximum message length in blocks. The PSK must therefore be chosen with
sufficient entropy so that m + log k is prohibitive for attackers (e.g., 2^128).

## Domain Separation {#domain-separation}

HPKE allows combining a DHKEM variant DHKEM(Group, KDF') and a KDF
such that both KDFs are instantiated by the same KDF. By design, the
calls to `Extract()` and `Expand()` inside DHKEM and the remainder of HPKE have
different prefix-free encodings for the second parameter. This is
achieved by the different prefix-free label parameters in the calls to
`LabeledExtract()` and `LabeledExpand()`. This serves to separate the input
domains of all `Extract()` and `Expand()` invocations. It also justifies modeling
them as independent functions even if instantiated by the same KDF.

Future KEM instantiations MUST ensure that all internal invocations of
`Extract()` and `Expand()` can be modeled as functions independent from the
invocations of `Extract()` and `Expand()` in the remainder of HPKE. One way to
ensure this is by using an equal or similar prefixing scheme with
an identifier different from "HPKE-v1". Particular attention needs to
be paid if the KEM directly invokes functions that are used internally
in HPKE's `Extract()` or `Expand()`, such as `Hash()` and `HMAC()` in the case of HKDF.
It MUST be ensured that inputs to these invocations cannot collide with
inputs to the internal invocations of these functions inside Extract or
Expand. In HPKE's `KeySchedule()` this is avoided by using `Extract()` instead of
`Hash()` on the arbitrary-length inputs `info` and `psk_id`.

The string literal "HPKE-v1" used in `LabeledExtract()` and `LabeledExpand()`
ensures that any secrets derived in HPKE are bound to the scheme's name,
even when possibly derived from the same Diffie-Hellman or KEM shared
secret as in another scheme.

## External Requirements / Non-Goals {#non-goals}

HPKE is designed to be a fairly low-level primitive, and thus does not provide
several features that a more high-level protocol might provide, for example:

* Downgrade prevention - HPKE assumes that the sender and recipient agree on
  what algorithms to use.  Depending on how these algorithms are negotiated, it
  may be possible for an intermediary to force the two parties to use
  suboptimal algorithms.

* Replay protection - The requirement that ciphertexts be presented to the
  `ContextR.Open()` function in the same order they were generated by `ContextS.Seal()`
  provides a degree of replay protection within a stream of ciphertexts
  resulting from a given context.  HPKE provides no other replay protection.

* Forward secrecy - HPKE ciphertexts are not forward-secure. In the Base and
  Auth modes, a given ciphertext can be decrypted if the recipient's public
  encryption key is compromised. In the PSK and AuthPSK modes, a given
  ciphertext can be decrypted if the recipient's private key and the
  PSK are compromised.

* Hiding plaintext length - AEAD ciphertexts produced by HPKE do not
  hide the plaintext length. Applications requiring this level of
  privacy should use a suitable padding mechanism. See
  {{?I-D.ietf-tls-esni}} and {{?RFC8467}} for examples of protocol-specific
  padding policies.

## Bidirectional Encryption {#bidirectional}

As discussed in {{hpke-dem}}, HPKE encryption is unidirectional from sender
to recipient. Applications that require bidirectional encryption can derive
necessary keying material with the Secret Export interface {{hpke-export}}.
The type and length of such keying material depends on the application use
case.

As an example, if an application needs AEAD encryption from recipient to
sender, it can derive a key and nonce from the corresponding HPKE context
as follows:

~~~
key = context.Export("response key", Nk)
nonce = context.Export("response nonce", Nn)
~~~

In this example, the length of each secret is based on the AEAD algorithm
used for the corresponding HPKE context.

Note that HPKE's limitations with regard to sender authentication become limits
on recipient authentication in this context. In particular, in the Base mode,
there is no authentication of the remote party at all. Even in the Auth mode,
where the remote party has proven that they hold a specific private key, this
authentication is still subject to Key-Compromise Impersonation, as discussed
in {{key-compromise-impersonation}}.

## Metadata Protection

The authenticated modes of HPKE (PSK, Auth, AuthPSK) require that the recipient
know what key material to use for the sender.  This can be signaled in
applications by sending the PSK ID (`psk_id` above) and/or the sender's public
key (`pkS`).  However, these values themselves might be considered sensitive,
since in a given application context, they might identify the sender.

An application that wishes to protect these metadata values without requiring
further provisioning of keys can use an additional instance of HPKE, using the
unauthenticated Base mode.  Where the application might have sent `(psk_id, pkS,
enc, ciphertext)` before, it would now send `(enc2, ciphertext2, enc, ciphertext)`,
where `(enc2, ciphertext2)` represent the encryption of the `psk_id` and `pkS`
values.

The cost of this approach is an additional KEM operation each for the sender and
the recipient.  A potential lower-cost approach (involving only symmetric
operations) would be available if the nonce-protection schemes in {{BNT19}}
could be extended to cover other metadata.  However, this construction would
require further analysis.

# Message Encoding {#message-encoding}

This document does not specify a wire format encoding for HPKE messages. Applications
that adopt HPKE must therefore specify an unambiguous encoding mechanism which includes,
minimally: the encapsulated value `enc`, ciphertext value(s) (and order if there are
multiple), and any info values that are not implicit. One example of a non-implicit value
is the recipient public key used for encapsulation, which may be needed if a recipient
has more than one public key.

# IANA Considerations {#iana}

This document requests the creation of three new IANA registries:

* HPKE KEM Identifiers
* HPKE KDF Identifiers
* HPKE AEAD Identifiers

All these registries should be under a heading of "Hybrid Public Key
Encryption", and administered under a Specification Required policy {{!RFC8126}}

## KEM Identifiers {#kem-template}

The "HPKE KEM Identifiers" registry lists identifiers for key encapsulation
algorithms defined for use with HPKE.  These are two-byte values, so the
maximum possible value is 0xFFFF = 65535.

Template:

* Value: The two-byte identifier for the algorithm
* KEM: The name of the algorithm
* Nsecret: The length in bytes of a KEM shared secret produced by the algorithm
* Nenc: The length in bytes of an encoded encapsulated key produced by the algorithm
* Npk: The length in bytes of an encoded public key for the algorithm
* Nsk: The length in bytes of an encoded private key for the algorithm
* Auth: A boolean indicating if this algorithm provides the `AuthEncap()`/`AuthDecap()` interface
* Reference: Where this algorithm is defined

Initial contents: Provided in {{kemid-values}}

## KDF Identifiers

The "HPKE KDF Identifiers" registry lists identifiers for key derivation
functions defined for use with HPKE.  These are two-byte values, so the maximum
possible value is 0xFFFF = 65535.

Template:

* Value: The two-byte identifier for the algorithm
* KDF: The name of the algorithm
* Nh: The output size of the Extract function in bytes
* Reference: Where this algorithm is defined

Initial contents: Provided in {{kdfid-values}}

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

Initial contents: Provided in {{aeadid-values}}

# Acknowledgements

The authors would like to thank
Joël Alwen,
Jean-Philippe Aumasson,
David Benjamin,
Benjamin Beurdouche,
Bruno Blanchet,
Frank Denis,
Stephen Farrell,
Scott Fluhrer,
Eduard Hauck,
Scott Hollenbeck,
Kevin Jacobs,
Burt Kaliski,
Eike Kiltz,
Julia Len,
John Mattsson,
Christopher Patton,
Doreen Riepel,
Raphael Robert,
Michael Rosenberg,
Michael Scott,
Steven Valdez,
Riad Wahby,
and other contributors in the CFRG for helpful feedback that greatly improved this document.

--- back

# Test Vectors

These test vectors are also available in JSON format at {{TestVectors}}.
Note that the plaintext is the same for each test vector. Only the nonce
and AAD values differ. In these vectors, `GenerateKeyPair()` is implemented
as `DeriveKeyPair(random(Nsk))`.

## DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 6305de86b3cec022fae6f2f2d2951f0f90c8662112124fd62f17e0a99bdbd08e
pkEm: 950897e0d37a8bdb0f2153edf5fa580a64b399c39fbb3d014f80983352a63617
skEm: 6cee2e2755790708a2a1be22667883a5e3f9ec52810404a0d889a0ed3e28de00
ikmR: 6d9014e4609687b0a3670a22f2a14eac5ae6ad8c0beb62fb3ecb13dc8ebf5e06
pkRm: a5912b20892e36905bac635267e2353d58f8cc7525271a2bf57b9c48d2ec2c07
skRm: ecaf25b8485bcf40b9f013dbb96a6230f25733b8435bba0997a1dedbc7f78806
enc: 950897e0d37a8bdb0f2153edf5fa580a64b399c39fbb3d014f80983352a63617
shared_secret:
799b7b9a6a070e77ee9b9a2032f6624b273b532809c60200eba17ac3baf69a00
key_schedule_context: 002acc146c3ed28a930a50da2b269cb150a8a78a54081f81db
457ac52d5bd2f581cb95a2c63b1dac72dc030fbe46d152ccb09f43fdf6e74d13660a4bd8
0ff49b55
secret: 3ed37d4c4c7e3ebe6cb1fca03eabd4c878b442da340915d51d6ed49d8369d785
key: e20cee1bf5392ad2d3a442e231f187ae
base_nonce: 5d99b2f03c452f7a9441933a
exporter_secret:
00c3cdacab28e981cc907d12e4f55f0aacae261dbb4eb610447a6bc431bfe2aa
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 5d99b2f03c452f7a9441933a
ciphertext: 9418f1ae06eddc43aa911032aed4a951754ee2286a786733761857f8d96a
7ec8d852da93bc5eeab49623344aba

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 5d99b2f03c452f7a9441933b
ciphertext: 74d69c61899b9158bb50e95d92fbad106f612ea67c61b3c4bef65c8bf3dc
18e17bf41ec4c408688aae58358d0e

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 5d99b2f03c452f7a94419338
ciphertext: e6602db9be05d81c4ab8fa621bc35993a7b759851075a34b3bffd2573400
11c70c9fa1f5c11868a076fc3adb3b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 5d99b2f03c452f7a9441933e
ciphertext: 71b51365cdd10e13883b12811d31132e5fbe39f9bd19c414cc0dfd81f853
d11dbb3fe70bb3bb93210f4785e27f

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 5d99b2f03c452f7a944193c5
ciphertext: 2cabaf3c878715e4fd81233753178b67210267c6468cb47d1385c3795997
f17ec871267abbcbdb920ffe8a315e

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 5d99b2f03c452f7a9441923a
ciphertext: f49d01ae618057302fc2652626e563cbaa849381b1aa8f4ae69dc5778c9e
c7751ac755f2f486241d150b969263
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
be82c06bd83fd6edd74385de5a70859b9e03def4c7bb224a10cfae86087f8a25

exporter_context: 00
L: 32
exported_value:
82cbfd3c2b2db75e2311d457e569cf12b6387eb4309bca8e77adb2f2b599fc85

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
c8387c1e6ec4f026c7f3577e3f29df51f46161295eec84c4f64a9174f7b64e4f
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: abd63dfd2fb9ccf8789cae5a6aff91e07f9f5925c27f005e702bf956b0000a85
pkEm: f16fa9440b2cb36c855b4b82fb87e1c02ce656dd132f7a7aec739294b6912768
skEm: 4c1feed23e15ec6a55b8457e0c0f42a3a1ab3ccc309b7cbb7ac6165fc657bd3b
ikmR: 654e8b44e8e29fc75f3beadf7f28dc065e38a53c1a731e15f2d46fd6130574da
pkRm: 13c789187a2dda71889e4b98dc5443624ae68f309cea91865561cfa207586e3a
skRm: 8e5430f0d821407670e5e3f6eecc9f52b2cad27b15a5fad1f3d05359ae30d81c
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: f16fa9440b2cb36c855b4b82fb87e1c02ce656dd132f7a7aec739294b6912768
shared_secret:
eeca0089c3e7d96d31f7c492f719a7a6cddec0170e9aba954c7ac8ca98388e0d
key_schedule_context: 01deb296ccdb4fa0a001eef56dd3b10577b30352610d1639fd
5738efd4acb8e4e6cb95a2c63b1dac72dc030fbe46d152ccb09f43fdf6e74d13660a4bd8
0ff49b55
secret: d09cfdb666083e43919c63130bc51234fcb1111f23795ac299cf60353447492f
key: 70030b55bfb737d4f4355cf62302d281
base_nonce: 746d5e6255902701c3e0b99f
exporter_secret:
716043e2ac96b23e6f12983e11b6894e7b7dab8a9e40976b467c514f59700d9a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 746d5e6255902701c3e0b99f
ciphertext: 63f7ed3d99e625d4a7373982b5f04daf0c3dfff39cac4b38eeb9d5c225cc
3183bdbc91a053db9b195319cc8c45

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 746d5e6255902701c3e0b99e
ciphertext: 65e7160f80fdf47893a5abe1edcff46c85899f04acb97882e194ce6d4fce
ec2dc4cb2d3abe5d969880722859b2

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 746d5e6255902701c3e0b99d
ciphertext: 915e08e6e340fca64982e90ad93490826bfb74af8f48062212c87105dad2
b7569c83688e564ed5862592b77cdc

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 746d5e6255902701c3e0b99b
ciphertext: 2dfc4bd86f24d09126959252139a5cb19a39995b68e3babbe331a512c6f1
a18e4b02f5f38423ac63a0c1e95809

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 746d5e6255902701c3e0b960
ciphertext: 5489a14805bdd8e4012e89d7e5de3f5831fd4b9ce02c108df8245fb5c7c6
f48120f2fce32201c2ead19baba011

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 746d5e6255902701c3e0b89f
ciphertext: 298dbeb43b37066d7d4694a44382d6c71bace7b81e11ae60f49f925f9038
74a8387e6be66a20439c66cdbfe832
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
7c40ceb745e14d19fceeac6e4756c796957fe5ff28709198c3f8cbdb5d368fe1

exporter_context: 00
L: 32
exported_value:
1ef0fd07bd40326f1b88f3545c92969cff202ca7186b9fd1315241f93fcc2edf

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
997368419db9490aa96c977cdd90bda8fd6234054d4add3d2f31aaaa2f8c1172
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 42d691088397246b00e9d9ce8f5406a317433558dc28132e02618970005d02fd
pkEm: 96f2d7d320decc5da12913a8251104fb4a410af12428a2c4f6213e568bc2f667
skEm: 6cdeec1514dd68afb70e7f2b14885acab48dbf997cdf6f367ce2ae551a6b627f
ikmR: fb953f486ef5f7a1ceddff40bffe02b857c8af9d611966e417a24d6efa7c9d1c
pkRm: 2b91c9e32324d39a018df09cd0a542b3e084e138a5f07f46a72f97e7fb7b0f04
skRm: c60d9ae57ca4dbba20f6f66afee34b0032bb6ee20c12c4801a3add63150ad746
ikmS: 131aa907c85b05726e7a058b064bf29cb2cb72a2afbffbd8076a884291f3143e
pkSm: 8e3052be1d6dc84f542a787b83002b3d57f4dc80ff4d1cd5e7d42d83c1e9b809
skSm: 639e6c9994f499e17eaf385f06d412fd8c2f74e17636b17ddeb1dffb0d6bfeee
enc: 96f2d7d320decc5da12913a8251104fb4a410af12428a2c4f6213e568bc2f667
shared_secret:
372455d46f8b665bc6c1335c9aef7f82289c4f0f75e3d934f52961404449ca4e
key_schedule_context: 022acc146c3ed28a930a50da2b269cb150a8a78a54081f81db
457ac52d5bd2f581cb95a2c63b1dac72dc030fbe46d152ccb09f43fdf6e74d13660a4bd8
0ff49b55
secret: 2d13ab71ea12f2dec7645f42f558cb0c791bd2cb4efa5e388d8bc9becd907a94
key: 1fb76aa488e82d61a1bddd9c0be51299
base_nonce: 5c4cf7f8b977e3b820a2555e
exporter_secret:
6b0d8f39bc80648a1ec0d2061afcb655358f66fa78fa826731d5dd58d22f1478
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 5c4cf7f8b977e3b820a2555e
ciphertext: e0d7a2da87292d7f3266a3d4e111af43baf5b72e0bf34c6a301d66a20f52
b84ef752bf2a4e9be760cb5f1664db

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 5c4cf7f8b977e3b820a2555f
ciphertext: 014430e7ea83f18570a4a523245b7aa1f7ca058ab6a78f7fd348e80e1359
e966cfc327b683f5c8e2c6525fa525

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 5c4cf7f8b977e3b820a2555c
ciphertext: be2c05cbb61276c68469eb482b08f8c2974c2df185e44b5cc526ee411ef4
57304d86b6efafac85daf8f19bdb7e

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 5c4cf7f8b977e3b820a2555a
ciphertext: 8111e411693a73884a25673e0aa423701634d10dc4a27843a93e2e9d745d
d74072de63afd0d7999d34ab463b31

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 5c4cf7f8b977e3b820a255a1
ciphertext: 1e4f396ad6d1537c3fda112e1311e6f79914fd5c1651620dc8d88cadddb4
bbd9b57d4d24bf6b043685b82f5b64

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 5c4cf7f8b977e3b820a2545e
ciphertext: ef9a271a5e2481228cc85270ec74760daa952ce233846cdc58321f4eca1a
8166a2f0c25388262373a659bc044a
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
e7144368d4722037591022b6ac29ac1a8f530a76dcfd8ad0d395501e7c5e8fb5

exporter_context: 00
L: 32
exported_value:
1725c4cd5e7f3cd5764d12dd1d9628485ed06a0db43b8b71e169177b905622d4

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
175eb5d853ed45eb38934d3d3fdd5b9297711fba6b1f03224d7b1b3b24dfa8fe
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 0c3a14fe896a7166f4d5e2a21c903b69f9ca71783290ca10f1b8c5eb258149be
pkEm: 073dc67ae68dec787f15bd37049cde739292efe95f5424d5a4cc1a1fe64a262c
skEm: 4ef985b4e27405436f849731258af97a5f4f286a3caf1ebe6222e166d132e884
ikmR: b759021868fba28c1ddd509eaac450a896ab0f5edffead0a019fecb574950d64
pkRm: 99c4a48235a345f11dd05ae39a142248af70abb88ade8004de38521328975212
skRm: 45baf5fb10484279eaad27c931bd2951065952829b79546d046f12637ce8fad1
ikmS: 2e7219703b6659698e4c2d141d13e0092df7039212db9c97e347c7d2c0aee239
pkSm: 08dd3ff3cab7fb8d530ac02474596cd72dd71c3bc0254bd1c8cd37ebe65b4312
skSm: 821c5beee84061b34016bd55c957fc4175754fde521e0604de7163a5d1c7b428
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 073dc67ae68dec787f15bd37049cde739292efe95f5424d5a4cc1a1fe64a262c
shared_secret:
aa853495243000a36aa1be4731b3eb14813794433fe18bd78057e314d6f682ee
key_schedule_context: 03deb296ccdb4fa0a001eef56dd3b10577b30352610d1639fd
5738efd4acb8e4e6cb95a2c63b1dac72dc030fbe46d152ccb09f43fdf6e74d13660a4bd8
0ff49b55
secret: 625974aec089efecf8625256d999db5fea57a935d338bdbe4235339b5c5f9d90
key: fbe3c9277490b6ad5b69b372fa0dfe13
base_nonce: d1fbd77027365203a477ceb4
exporter_secret:
5745f3469e3518ca6d34880c72185fb64170e4b2d07f168fb451a453a993161a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: d1fbd77027365203a477ceb4
ciphertext: 03fcb03822447fbf52a5b951ffe1f615a428cfa9bda02297e19e7fb959c5
440ad39ace9d9f8b84917248842559

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: d1fbd77027365203a477ceb5
ciphertext: 58d0c84286319ea43ca1c362cb04fb81df33ca85c5b9d1ec99986bff1882
be6a6ebc5c5c3a2f46dde0a3bbd8aa

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: d1fbd77027365203a477ceb6
ciphertext: 922fb5157aaa9e27c61bd505be4a1ff7a55ae94caee77a195417aa467d34
c318a35f956820e2ad3579487b4211

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: d1fbd77027365203a477ceb0
ciphertext: 23581839629da5cf878ed3cc67feb6ba60b650fb1b5b0d1df98c65496258
0ff57ca797c7d8a5b32d871fc81469

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: d1fbd77027365203a477ce4b
ciphertext: f6add683e306145f0c0107c65014b3bf72e3c3d0bf988e31471cef869f4f
cf0abf7daa59e5b1e932c865ae6a10

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: d1fbd77027365203a477cfb4
ciphertext: 63c770333ac20e56ac84d6a7371836ad4c942f6d1386cd1ca9433333023e
7203a9583df04875aca35a0fa49014
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
e8968c8558146edf379954a674c71e7b2d713e0a39d45b783b10af55492f54ab

exporter_context: 00
L: 32
exported_value:
fef7d33a45fdd148a4f8f12d18405539957326f6f0fea0ebdf6b37f25a9238b8

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
aad4715950a355afd7e44e27c17b656088b1801e8b3c61f5e5c4722b5e28ee47
~~~

## DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: d01cb3b75c48f80151f4efeb972fb2097f8efa64d29ca70f10f51e116cb6ef31
pkEm: 1440805f4e60cbd34835baf0813c3071d17def1dbd8c04e75889bb2271d7823a
skEm: efda8f0538ce6ab9f165aae26e02ad96dcb1775b248267174aeb3d140e002ee3
ikmR: af2dfc6182ef4bdc3ec2118a0c3d0dd7daf2f2dfef6706ca861fafb5415e6b78
pkRm: 26147d5c2978bccc3cc03a4f9ac607560b5d83f852be4e9024f2cb7207d4c30e
skRm: 14365bb26500e7cf263720c4ab04bd45b8e146b4f724facd1fa01d58b63975e4
enc: 1440805f4e60cbd34835baf0813c3071d17def1dbd8c04e75889bb2271d7823a
shared_secret:
5f32519d9ca90b0572df7aa3b2e2f35376cafc61e027a406e03d6441ab818a7f
key_schedule_context: 00dd0a37ad96727124b021d7c81c42bfbb68c11f38050b13aa
54adb5a92dd165760f0d33c7dafc645fdc165ad9d110e77f68358179ad974a9a9b71dd05
5dec5eee
secret: a8c7098db69fc65995338ef616bd4d3c2bb4ccbe0ee91294f377df65893d28d3
key: a17448a542d0d6d75e3b21be0a1f68607904b4802c6b19a7e7e90976aa00a5c8
base_nonce: 6f6b832dba944a91e5684514
exporter_secret:
bbbd4216184bd12888e0cec08e384c2e39639fe1527f220f3aa751f5290a9aa7
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 6f6b832dba944a91e5684514
ciphertext: 1b9ce69bd0e6b4242ac2dd841ef093fc9dfa9e684f81c2d1778fd3268ca5
aa7d612cd87f72acd2aeaee084dee2

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 6f6b832dba944a91e5684515
ciphertext: f041fb8de275b5319587269cb39190029906b9267eb5619b7bec8a5e0b3b
3a0bead169617f2c4d45d028b1b654

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 6f6b832dba944a91e5684516
ciphertext: 0042c74002608a20e432ee9628e84cba76482aca29359e93d60067371be5
47355acca2c271a2072b85a77a6237

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 6f6b832dba944a91e5684510
ciphertext: 1d38eb05ddf406b77385c264e5424cc812de6deeb46990ab811013768100
95fb175f6a5bc18b70ca59bdd33fc1

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 6f6b832dba944a91e56845eb
ciphertext: 7f25184ece5359a927f857b449c97d07438461418b38f75438a648b81ca6
3bdc8903289a1b14e276c9c320d018

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 6f6b832dba944a91e5684414
ciphertext: c8a9a7fbfc865fe1de53349e27533ea957f20e8ac9617f389aa1db20b7c4
a60291bdacaa9405332d8d416ee535
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
996dc6fda1dc47e687613e0e221d64a3598e1ead9585177d22f230716569c04d

exporter_context: 00
L: 32
exported_value:
6d07b4e3e06ace3dc3f1b2a0826a0f896aa828769ff993c2e3829ae40325c27d

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
bb69068c4f7767331512d375e4ab0ca0c6c51446040096ea0ae1cc3f9a3f54bd
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: d820fd699360f7b65024a0cab8df9e2444a78b9f050305329f9c26ff02a0513d
pkEm: 8e4b29035c22b67b3a7a0f5a52f12b3ab17a9ae1f0c63b029137ba09f420224a
skEm: db1c9dfba77e1e3b8687ea18af207cffca803bdd983f955376b8271ef9c78a46
ikmR: 3667287b229ce92386c1d3fe5b58f61e72eeef983dd02220f29c75bc8fed6ccc
pkRm: 94ea1227a357dfd3548aadb9ef19d9974add594871498e123390a8bcb4db5d51
skRm: 4e335da3ec60e68c156586b8217de6801cb83b5a4de413645fcb112c00b2228b
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 8e4b29035c22b67b3a7a0f5a52f12b3ab17a9ae1f0c63b029137ba09f420224a
shared_secret:
f2aa15c783c62c7e55485a61404d8beae0644d15042848e5adf3d315981337e1
key_schedule_context: 0151af0d3a80f50ff5d606ae45bf724c2f872698eacd389476
90bf75e1262a72a30f0d33c7dafc645fdc165ad9d110e77f68358179ad974a9a9b71dd05
5dec5eee
secret: d5c8a90c9d1ef47662ddbbad6a8e8722194a605017718fab2b0172eacc51a4d3
key: a603fe0f9897dc6ce042a467d6bd430a01cd679e930f1b5706ad425e4153496d
base_nonce: 318e48afae42913a928146e6
exporter_secret:
965e593816181bd8f14211f5e5773b3fa256a24972a1793165177987cb82cb6e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 318e48afae42913a928146e6
ciphertext: c87f8158a501c7a2f31708bbdba10f9c5ad035624c3153eeb028e65b82f4
1f38cbe1cd9aafb10e502d328b83c1

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 318e48afae42913a928146e7
ciphertext: aef7a0b0e3a58b177dac9628439b44d1e706724e265ab3b46d791612b516
37342479ad945607b8b54112bd8c86

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 318e48afae42913a928146e4
ciphertext: c00884a5c658213bd4381d65b54d93682692fef9408a6e437a97a9042677
27269b242d3d81725ad8f0c764e082

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 318e48afae42913a928146e2
ciphertext: a867345a23c686e141d0e4a754a8b800c79cfbe854c95ab52e41ccc61e18
787e0ee7ab42d53390b2ca0508e3b1

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 318e48afae42913a92814619
ciphertext: 3eeb72e8f8dc6b792529042b0f74c17e8dd112bf1aaa1a17179359931fb6
81bd35cae9467bdda5d05a77be344b

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 318e48afae42913a928147e6
ciphertext: 17b14d194a1f3f243a9cc21c19484f86b44f558dc0ffee8a06ef2085b9f7
d4908881fd80b0ce2c73f680a6632a
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
23c31ee2757bbecf105f74c90bf1e640b6ddc545dc8d80b1abbf2aa9dd1786ce

exporter_context: 00
L: 32
exported_value:
05af7597519945fe8443f7cb84cdb651a8dd18cd7bbbd65d31095d3c69c1257e

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
5814619f842c7c328c9657854154e51b581c7bbd3b646bd773be67f93900a109
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: a7ea00294fd58b6f17cea5402a8301cf8f13f31fd7923da79e4d22fbdc114a10
pkEm: bb693083e02109b884e823a43cc5354810c74c14ef8096e2b2b46dbdbc1f0354
skEm: 81a126244b2fdbe305a344f96a4d4c12db3516abac07237595e0951194303fc9
ikmR: daf40bb219e0672b442e93f0dd142be3f6293aa5f759bdd659be59b2670183e4
pkRm: 57c3eb0f67944545c6f87e813336fad0ca292876b033686e49333c7b7969ea43
skRm: b127bc7ce70fb29c32afe4afccfde11a86d87b75056f76a9cb2c12c56e230202
ikmS: 8548ec6ef3eba79e53eee89776c8a954421eb56ad037049ba6a71345ac4e4d7d
pkSm: efb2383804afaa8b10ed364917013af2f7bee72b45f3fe3436158bfe5b48c556
skSm: f07411fac6c0e43f727873b3ca7ec1e6dc18d47d7252bbb7efa363254523878f
enc: bb693083e02109b884e823a43cc5354810c74c14ef8096e2b2b46dbdbc1f0354
shared_secret:
9b8dedc0eea8669e6619016d5b507ebbbdf88f2ae7e56ab5419c6f7b730d3c3b
key_schedule_context: 02dd0a37ad96727124b021d7c81c42bfbb68c11f38050b13aa
54adb5a92dd165760f0d33c7dafc645fdc165ad9d110e77f68358179ad974a9a9b71dd05
5dec5eee
secret: 88cabbab550b94987d062601f348559c9ffe39ea74f8b197c634abccb6e2150e
key: ae2acf842b01392303b1ac325a0884bdc66221561773e78b3f90bfffc7b7cf6b
base_nonce: 51e9a58b065bcaeb4bd5ae3f
exporter_secret:
91146b6874694292df424bc1bacf4eae19ebac1046f3c7f28d77fd14f769a30d
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 51e9a58b065bcaeb4bd5ae3f
ciphertext: 95213d48a449db6c76c831970154e31ea368344efb257635aa2b8f04b621
77ecdf7544d4905d24251c5f2633e0

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 51e9a58b065bcaeb4bd5ae3e
ciphertext: d34c6735d87abc0b4dfe45436f8ab1dc9267906887bb02f7a18e3bab7487
83873589e9872264dbbcc41e4c5450

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 51e9a58b065bcaeb4bd5ae3d
ciphertext: d31f5c42c15ccb0b78c7cb389ec7ef581b02691288f3e4329ad65c5845b3
e4c023d5611e87aec983060329fa78

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 51e9a58b065bcaeb4bd5ae3b
ciphertext: f0e8ee58337724257ba191aa19b6db229ad2b2ef1b35af710833897bfea7
d2366cf07982bac7202f73d1422e02

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 51e9a58b065bcaeb4bd5aec0
ciphertext: 688a5c8223cfb7f1af032bbeb146b40c90734b47b956e633c7d9f7c3d54f
5c74325cd81072a9bd313f096be0ef

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 51e9a58b065bcaeb4bd5af3f
ciphertext: 6bd76cc851f39c00dbdd4abc8fe016321d487f600968665bbc40f8459a0f
ea56cb07665b92383de6f2d2a6f6e9
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
da976957d7d640eff1493ae7447c6029fc49544e877b2355ad04798a9534a214

exporter_context: 00
L: 32
exported_value:
be6de0f31f14a514ad7b39128dd3f8aa147a6404273ec4e8f93b4008752a4d29

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
d8d13d7a1fc443a25e17c9d4e76819a771c028e98467258853980d56bea40c67
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: ee151f6f9d7675264c9b3a6e79d693e30f30fcdd2da490b173728e02a96ce94c
pkEm: 15119783fec42323b69bd9366d08728c3235a33d7b5efd13696b2cf24ae2d326
skEm: 4e2331094c64808028d9faf3db953e07c1ab699865b9f2e4932ef6c5298c5e8b
ikmR: 1bf7a5146de616c717448ce90858a1b42460d9208f91bdb7ebcd88f3b258c888
pkRm: f615ef89a538025819d3b59e9d7feaf08ceb32bb6e25e7159dcb2c5327713040
skRm: 0e465977bdcaf8bd22a234c047b0c57e7faa5d706e8259f8350b188b79178a8b
ikmS: 9640d1d632eec4fec539da6329d835e799ab689aa81ff90084dcc8dd642aae67
pkSm: b3f4381c28453f8f9e7f5f6748282d210ca9aab14a1af8b70396940a6bf79514
skSm: ea8a1964469e94548e2e7923199479cd835d6c14ab972ea98fac4d5e4e7985e4
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 15119783fec42323b69bd9366d08728c3235a33d7b5efd13696b2cf24ae2d326
shared_secret:
6c8ee916db78a8753e39c16a9c7edcc0ddd3cf74de4724c1a2d48db4e6117781
key_schedule_context: 0351af0d3a80f50ff5d606ae45bf724c2f872698eacd389476
90bf75e1262a72a30f0d33c7dafc645fdc165ad9d110e77f68358179ad974a9a9b71dd05
5dec5eee
secret: 9b53a68e242161dfc6e39ed4fc8fc6a697cf4148016f3b2a887400c3ab930ec8
key: bedc7ab24c27e4a352fdee21a72037018f1d7da58e8b559a05ead86a373a0acd
base_nonce: b2d8ee6f49682c201478ffe2
exporter_secret:
5354659d14b4a5934c148648ea5a1892e9210f0aa0913edf0b928c8548acaad5
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: b2d8ee6f49682c201478ffe2
ciphertext: c16313e94c81ad5cfba39c61b0a92555de7bf7687a33c846571ef41ea394
76cd9de8333f490b90137505ee7f1a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: b2d8ee6f49682c201478ffe3
ciphertext: 9f3a6d1538b98efcfcea7e639d3a296de0b884b4a72e8de66c82b487d969
a190b8ce289b3da0a35ce0fb442cd6

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: b2d8ee6f49682c201478ffe0
ciphertext: 44442489d1e3d0d457e4791345fcd9af580f37543347e410e5c3aad6f2fb
b0e4bed75c30c529917b6ae946128d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: b2d8ee6f49682c201478ffe6
ciphertext: c3e98672a8b26ccd0f88a98b08dcb5d2937c059441dd3a511f79255ebcdd
f03506d6b686dda63280f50b8dd128

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: b2d8ee6f49682c201478ff1d
ciphertext: c321b3fefc2b5db66da44993f4a2ac7b00960d1832ef08129732b09a3648
0bd142405daada3971e4c2f206b487

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: b2d8ee6f49682c201478fee2
ciphertext: ca68883d2acf213cfe68fa09a3f8d366ea51463d64279d266e2e7c00ccd5
7514acc9f3680b9924d8a91259eb52
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
d29bbb7ec1acdaa89e0a640a95060f42beb7f7e462c3b637e7a875945da0d490

exporter_context: 00
L: 32
exported_value:
a22dcb81ba0ed07ae2d8893e081d22a7a44c3651da561bfa0c34f1fdc66d93eb

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
9865bccc8c38f8c4273e7c1afb67bf1a877542473c8d861de8215d63dc6c8b91
~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 217684b3a5dae4e826b32f539381aaab0fcd4829319beffbf60f7e52ae9ea7d1
pkEm: 043da16e83494bb3fc8137ae917138fb7daebf8afba6ce7325478908c653690be7
0a9c9f676106cfb87a5c3edd1251c5fae33a12aa2c5eb7991498e345aa766004
skEm: 03e52d2261cb7ac9d69811cdd880eee627eb9c2066d0c24cfb33de82dbe27cf5
ikmR: cc82b085f48f5fc966237b8fd9f88f919b3ecb7067937e6e051316759652446e
pkRm: 04dc8b502e23e9bd533918ad19238aa39e334f5fac3114875fcf3be3a67f003fa5
215d39a8bb0d42e2a883a0b7f3cea08bf73aaa3b3e057ab6db766e75d2a141e3
skRm: 579cab9fb3cede795644e91469d6bb0a61dded7c8737bcbae428d7b4940bdf72
enc: 043da16e83494bb3fc8137ae917138fb7daebf8afba6ce7325478908c653690be70
a9c9f676106cfb87a5c3edd1251c5fae33a12aa2c5eb7991498e345aa766004
shared_secret:
49fb00067f3f00cd750a310038a4d4b80b79119a823bfef415defd2d524aa1f9
key_schedule_context: 00abdc9c4089964f95ca07f84a7d90d1864490d302249bfb20
7a247b89813e9d1e4adacd502dd077a8465b84cced711d5a741aace2f80a9ac865043442
2fe23927
secret: b692c66d9d7d55aab582e338f2b1eebea189b31afe21cf682f7bd012f2bff755
key: 42794156fa4b990dacda4e1625b52f9d
base_nonce: 8f56564f842b8bb03cc426b7
exporter_secret:
b5ed294c49327fd46172b0623a01125432a51d6447cf053c57ca1de30df7352c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 8f56564f842b8bb03cc426b7
ciphertext: bec8250980e4e092e821bb9e90d2ad445980048bde2419355315cefcc9b0
18aeb9912df99483dabe0927bcaa0b

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 8f56564f842b8bb03cc426b6
ciphertext: 8c3476a017d986bb00d1675cee7d051bf68e3a27311463a0fd59c44d66c6
1c34a205702f29a7476fc8bf12a03c

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 8f56564f842b8bb03cc426b5
ciphertext: e7674cc026ee19360f08108f9bd54b5d4c6aabf94d0b350d319d9cd9bdd9
c41e4d807e76d7f9ffff5c6a7416e3

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 8f56564f842b8bb03cc426b3
ciphertext: 401ab30e14b87c8b5ce90eb7ee8a1800ed4d5034ab6afe792a1df81b59fc
65151c6ed4847015aadf7423d395f4

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 8f56564f842b8bb03cc42648
ciphertext: 05204daeb0a306473e6c6f176ced15b2c31d34fc4a20be381dec69f08800
c72a64573da0a23242f1dc7fbc05a4

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 8f56564f842b8bb03cc427b7
ciphertext: 9ae29c3bc3bc545b490f743847e0aff85ca76991c88a1584387ab8a6278e
4f02e550a62fcca9dc541563c63340
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
69621533ee044f8715b37171e9a5f553b8533899fc0fc73c5856b99c8594d88b

exporter_context: 00
L: 32
exported_value:
cafdd05454242eab5b23ecac1705bdd56162906522e7e3f18461ad5a9f6f223c

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
b568edc82226d209d8509d101bd7b07db37f3f736eef50e0586551def45843b8
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 87de910e077b5ecd0bc741a716cb819dd10fd1b9641030cc34b73e15f5b82419
pkEm: 0409cbb5d409939003aa30d4e59b5664381fc529bc4b92d026efc3b2ac59405594
029d7456d30d14547c627a6f6aa9db346afb8fa8f49b78a0cc1f7e16d63a26bb
skEm: 5055721c0086cab0ac1b36b79c15daaf558ba3b6f720feee8cf9bce450dda2bc
ikmR: 2faf0aecd41afb526fa7ecb859a739ddf0ba11fccdd262d751c5921b9bab3c2f
pkRm: 0475072da3e5d06e61a356af605cc937ec9363fa3c4faccb309afc1fb7c001a7f7
08d8c609a05327bd07c05dd4ad258d8e1e5ae21d291bab1e00769c8b7948353e
skRm: 282b4d09b5119171becb6bf99da831cf1ac81aad27f6ce80ab795ec895cb3bec
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0409cbb5d409939003aa30d4e59b5664381fc529bc4b92d026efc3b2ac594055940
29d7456d30d14547c627a6f6aa9db346afb8fa8f49b78a0cc1f7e16d63a26bb
shared_secret:
85a8809b1a7ffdd2be2c61cfbb5256a4dcb9c04f05bdd711b575e8ba3352058c
key_schedule_context: 01b1ef02398e702f654bf6f28d9825bef0e545000702cb1839
b14bfe7c754c501e4adacd502dd077a8465b84cced711d5a741aace2f80a9ac865043442
2fe23927
secret: f33646dce5d6c3d4ab773f280eb90b0711be5d1ec7c8fa70e25f6d0fbc4658f2
key: b2bc0d3b74a5adaa215a56ee24bcd5a5
base_nonce: 92b4a0c272b1b2ac88a78c9c
exporter_secret:
e2dcd92c807e115f30e6ce2f931c9b7703354205aaa176ef9d439c8688830a70
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 92b4a0c272b1b2ac88a78c9c
ciphertext: ef8f226aa672114a81dad68f8dbaa0464d581723f7572cf8d461601013b4
0cfe91fb29266f66a8b28769b865a0

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 92b4a0c272b1b2ac88a78c9d
ciphertext: 04d33b9e0719a90f9b9fcffeaa572865eb9700be7bd629f838c54d09f0cc
e8abff1aab35fc146982206dbad974

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 92b4a0c272b1b2ac88a78c9e
ciphertext: bd6d4efe598c3569fad97eb91dad048e21fd6751da6ef82f0d359c2b026f
e67f4cafa4dde786fe38a21b93aacf

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 92b4a0c272b1b2ac88a78c98
ciphertext: 9f74c91b24a277ba3712b4f2fc24b30b5c862436c9c6012a3552e88a99d3
18d2e8f328cf812aa019f2fb35d996

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 92b4a0c272b1b2ac88a78c63
ciphertext: 85a0f219128bb6473266c1727d957209ce03af2615eda040dc5f6ef84428
0dd7fae5301a571dc4cc5059b67cad

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 92b4a0c272b1b2ac88a78d9c
ciphertext: 346cb2255740dedd0712b5406a07a693becd7e5888fefd9b290481fe3e67
546918654cfb5719f0cb241269d47b
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
ac856c29f6fe37c8c8cd5a43f0bf089795155732e805386ac87268b820fdd5fd

exporter_context: 00
L: 32
exported_value:
a7d4a142d6449b0dbd59afd1efc2f628444fbb56e5bf472cb60ad7f2747e57b0

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
79820a63b55d5d3f7a3a40fb542c6c31d8180239cd9500c763ff2355e5f535a2
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 065d5319c2ec55de1961da81f2b1c5269fc0d3e91f6845116c67f8aa3b2359be
pkEm: 04343a6ee2de9b0a3a5526d2832a237e4c962e8a8862ca41f06b3d4abb95f7a327
400bb30ef5fb633dfb7777bc93c7a70097f77cbb0cb889a135b77174f3361894
skEm: f0f4a95f666c4acb2f4a95a88a94a43d0a0ef3c4730f73c003f1468ad531ab46
ikmR: 234e1581536597dc464ee28518c56da07a2520188d29fed4d4f22146e9ec0137
pkRm: 04e52bea06f7df551af20abd964320e8cff1ee8c2a29a25e6c18af57db6270d583
32f68faba6b81c65e8cc585456819dd831754fb60c617b4d6b75c381a87335da
skRm: d7dc1db5df0799cb10803e6d39e4994d09bbfa0a7a89a93efaa014b3522a7df2
ikmS: bad181a04924b176f973874c5d8a9fbefef99bbff0974bd08b5bb2bff7bf7e33
pkSm: 04014b9a1db837c79e9ea3d771ad7fd52647baaed31d0930acf2bc4e37ae8b9c10
8d07b36625944cf2db636af39ea13f02d90e54cc93acb6f81520dd7161b7cebe
skSm: 79b8d2219ad0aae321a523d44e848245db997de1d56210ecdb0f761572c0a473
enc: 04343a6ee2de9b0a3a5526d2832a237e4c962e8a8862ca41f06b3d4abb95f7a3274
00bb30ef5fb633dfb7777bc93c7a70097f77cbb0cb889a135b77174f3361894
shared_secret:
2e39bc45c156e72f6aff72104d138f7f7323430d3822880e196c5e12e80e405d
key_schedule_context: 02abdc9c4089964f95ca07f84a7d90d1864490d302249bfb20
7a247b89813e9d1e4adacd502dd077a8465b84cced711d5a741aace2f80a9ac865043442
2fe23927
secret: 8234f5fcb9b39710445a6fb4b14251f04eb019cde58799184419c128f189be26
key: 74bdf9a5e59a7b9fa7d2f79776c91ead
base_nonce: 832c6d062d1f68e58544b407
exporter_secret:
4e8f1ce833028ae349056fb95c8aaa1b439c89e66a12cd7663c488f1f57ded68
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 832c6d062d1f68e58544b407
ciphertext: c3c904de9d74651a19e8a205b683381c876a7b06d537454c2e04466e20ad
0e56551c463cbc6c03fc241694ccd6

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 832c6d062d1f68e58544b406
ciphertext: 3cee516a8d3306c889a34c4fd1822ef628c80ec4f1fb089538e69fbb5eef
bc9ff8d883b9ee4551644b693fb901

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 832c6d062d1f68e58544b405
ciphertext: b452541f8787888c8af2d58eff449c2cfb9d884b5425f88f7b09624da356
d08facf561b95105bec39e2e15fc7e

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 832c6d062d1f68e58544b403
ciphertext: 1357058b45507b5080444611be4a5def77123e48264ea8bd79ccc04910ac
4ab2f6802c3e15e18c292d4e91b71e

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 832c6d062d1f68e58544b4f8
ciphertext: 81ebbf73373305ae41c7a1f9ce46fff4404674a3c5968413409777658e1a
412b3d3ae1c6d08aaf94894986cb33

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 832c6d062d1f68e58544b507
ciphertext: 7b94d1787a4935286e6a04724bb6ef7825e0f287cb6ed26e82b7773e8dfd
0ef3aea99546358505c0a862cca3f9
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
45b8805ad41e8133decb2cf41f23bf3c394b2f36b1e94c7d2f088b68d106bd2d

exporter_context: 00
L: 32
exported_value:
bf22e7557268fe6e7264cdec6537c41c920da6486dfe6eb26bb40dc2ad39b0e6

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
3e110ec362b22cb77d455c5a5031e0708b4e8dca273626621f6210b39bdaa3ce
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: f8583351cdaf7ab4ec91ad306602d4822fd0f84a2e5ea563c360d4ba6308f93a
pkEm: 04dd8aae40c4286412f9ba7951066da54ea42c2cf21f83d66ec9b4ab3358637a18
797495bc8f717937e75d31846a585afda6113be5c82d9b8b0cda43f0a76d05d5
skEm: 0fd2397b795907eaaa63f9c5552af8f2032c5c7411ad2f7b5760894e4ec8d240
ikmR: 3b16243c4382065ef6fa0701442f80810ed68fdc361a13b953733d9ce82a9e4c
pkRm: 0464b4a0b01cccadebb4ccc46260699cb995579feed53241a7e210665b89ea9607
d978400eea20b4921b92eda98ad63fd55271304c28489ef2f7a340912ba49566
skRm: c58ac157b4d776628d34cf3aae37af91749e8ee8f7b20e79f8017c82a679682c
ikmS: bb16b05e401acb2d245f825df3317024aede39c92952a42c19846d97384f79ce
pkSm: 04b373ecb4a475ffac6efa4924c5b8327d47bcfc028dbc2be44b0c23c2eac7302d
1943d8d5a01991888103f0357c346b047cea6137aefb016cebdc52f58b72c862
skSm: 2d6b29b62182f18f3836945624e9950e2d1119f5b065f6ab98c9ecf869a3bb8c
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04dd8aae40c4286412f9ba7951066da54ea42c2cf21f83d66ec9b4ab3358637a187
97495bc8f717937e75d31846a585afda6113be5c82d9b8b0cda43f0a76d05d5
shared_secret:
b48cf089f62be3e5ec158c01f3d32788672d5de3f73f8116e02f501bd9abd545
key_schedule_context: 03b1ef02398e702f654bf6f28d9825bef0e545000702cb1839
b14bfe7c754c501e4adacd502dd077a8465b84cced711d5a741aace2f80a9ac865043442
2fe23927
secret: d93e46cc616af860a5ac36f4c8d7e1e2fe9a583b202f8e801b6def73f1a890f4
key: 393a59b50e6b394a4ca0c3f9bebaac7e
base_nonce: 96a5653db53e05025c7f12bb
exporter_secret:
b61db4f5d5118602108cbef98f6a51d0977cc166f070b9dd597269907268ab31
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 96a5653db53e05025c7f12bb
ciphertext: fc5101a56d1f28a6381079c46c4c701b34bd730be5ee55ad8d95a0692ce8
3a4c11ba991ef3fbc25026c2b2a9d1

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 96a5653db53e05025c7f12ba
ciphertext: 60c788f75deebe151eed8fc03256057b7b356c493ff0704b7db20372baeb
b8c89b7c10792bde2158d0ae0ea084

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 96a5653db53e05025c7f12b9
ciphertext: 344507d1afd34327600a3eefe793e4f320fc6d57a65cb9d6ad358078d94b
1dc7fa6c0ac1cf5045b3d34aa802aa

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 96a5653db53e05025c7f12bf
ciphertext: 485fbc3badb0a84fe12ffa0171834cb5873714317f31b793624586cf5845
056ca165fe2b2880cf0ebacddc84c9

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 96a5653db53e05025c7f1244
ciphertext: 7bba24051a704ba9044a86a2ceb6984e808ac8eefed6c8c124b07b78702c
c414be6e0c5d12ed67de261375a1d5

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 96a5653db53e05025c7f13bb
ciphertext: fb7b2affa7ad31b705385c1b7b728d8d2516fae09c653718965e1eb8e40e
eca7aac3d5d619900733952430013e
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
6a6206e184b6308c104d5ed4de17b8c460fb5ae6511e39a99e84d124942848c2

exporter_context: 00
L: 32
exported_value:
42880d4e3b9865cefe708472b3d58d8800f1e5ad31e5fd692173bf1622ebf635

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
e7bcbccc00c31a3e068aee4286aa280b473ce9fee3e9a46fdfe58b8feb9d4ba4
~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA512, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 1be1a54220f95e65d4865efc314753feab34d867fb922613506839698e165744
pkEm: 045703c14ae77d584727e31f1179c680977359ab12a8842344d25d70d94c989c7c
bbc0d2de9258ce4258d2841e5b80d232e5226d5788f25835e53301e4b8b32c45
skEm: b1f9adb16d96a4d6efb95aa42abdb92eceab5124a6690fd9a35969c59df77ff3
ikmR: a3a4746d926dd36270656e365e6914c9c0b22e447e2ab670f221700e3c880d9e
pkRm: 04fe24564aef5463d7fb4efc238a4c6029364a0fbfbfa2201eb935fb1e6ef7cf9f
5f3ecf4d98017c42d25ed11e5c37795c6996dbf79f54db013258373ea09ff3ff
skRm: 07df110dfe250958de0d46374bdbdb5df61fd5e9cec35a04ec45911cc674c7b0
enc: 045703c14ae77d584727e31f1179c680977359ab12a8842344d25d70d94c989c7cb
bc0d2de9258ce4258d2841e5b80d232e5226d5788f25835e53301e4b8b32c45
shared_secret:
d6785d582e6706b0e2695f4aa3cb2216865144326af47aef77c5f16938bf2115
key_schedule_context: 008bba5aff4a4a949c4caaf55df2daa905f5946efb46343832
6fb2dac8504145236cccff5a2a6115fd54f5fcb61614d951a1506b918aea54eda6f60967
8f4c506f0aa4844da0eb89cd2aecb3dd959e4e33cc9a46aa8a7aaea199f4e99149ac50b1
a05cd20c970376cfaa5e61479dfc4f1fb4d39ba794f274965065a79536faa517
secret: e407d8700ec99486fc20fb0e54d2c7684d6b78ea0e6bc3c91400f286527141f3
91285cb7bb8ed47889693c9485634b97a64c68bcee31c6eb5161d5ba9daeab7a
key: d0aa3853ec6a21814c2876a76b62f3c7
base_nonce: 8dd480f20352222b7f2b51be
exporter_secret: b5c030ccb103a70348dce847de662ab57c01519165b63f13c12e6d2
187ca5469077130df244e0dbc0f93fde972d9c39676e9c763272e28d3bd66366660386d1
7
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 8dd480f20352222b7f2b51be
ciphertext: 885be6ea1756ebeff3d0f2216cc52a193054a0c2b31f6d42f0e6025a2779
6e65336b6d7377819e70c0ce486ced

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 8dd480f20352222b7f2b51bf
ciphertext: ab40a05bceb8589e5466a7deb1fa27d208431ad6c8398edd95da19cb1231
b2f4151df79c121077ea54a8b57d0b

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 8dd480f20352222b7f2b51bc
ciphertext: 955c94ed7ef09a543a479e3de2a7b66549ae252c7fd605bf789b3e583c72
87f95af64437af607538a5291b0e32

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 8dd480f20352222b7f2b51ba
ciphertext: b21f0867b531a8ec9c6bdf97a1d87919162b544f5a6f72471c18c07c3560
52cb7941ece10717a2a8c92db15337

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 8dd480f20352222b7f2b5141
ciphertext: 568ef11857b20b6d94309be34592eb28dba24f9d563395a698bbf6b4fe42
905baf4101da7e0b478bd50478885f

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 8dd480f20352222b7f2b50be
ciphertext: f0a97864ce8261bfe18ef38eed82b702cb4455ba93cf9179b6c90e008ea8
bd1a38e98c8d1204211c6ee6273b1f
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
3523af5ece737004383d7583bbbd0e152d139ae3c5460d213bb0d6b521934215

exporter_context: 00
L: 32
exported_value:
26f64e97f5591c4aa215bc593ee0977b4372a894b6e07d52adcf4e27434dd45e

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
a94035e80df74969ba074d51539048a7e238df3e62b63d8be500e517b79387c3
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: c62c050ffc3573b9d0f5fe976afc913ee415b5746f9da906f205b591898e296d
pkEm: 04a9866332764dfb16d2ae5f6485a8d8198e5c7fe9f9c79e2728f59852648de367
309ddd35993229ba6201f0eeaa014fad860e8098eb29e2044fd80cbe04215248
skEm: 783de5184f6e61c4ea8ee688dc8e2b427869ef6d4472b134c12eef130df2b29e
ikmR: e06f47f500ee149266590166c52e3f35366542206a666579bc641139f1cbd2d2
pkRm: 04303656e359e35ff4c337ab17f6daefbe3a60adbe9a09608623a0d81c7d01a3b3
cd4de3e54fe92b039c98c86c3c5f1f4ef3c8d229375537bbedae8e26a9ed6f12
skRm: 090327ae0309d4fe19a3f1ab5c5cd2097f810b4dbad57a208408168588a44584
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04a9866332764dfb16d2ae5f6485a8d8198e5c7fe9f9c79e2728f59852648de3673
09ddd35993229ba6201f0eeaa014fad860e8098eb29e2044fd80cbe04215248
shared_secret:
9615d8a9ebdb765b07bb79656ee430711cf8fe7ed391767aa58de4ff5eeb29d1
key_schedule_context: 01f37d94392114a83426ed4ef40b204fcabab8c86d1541b7dd
7f71d1b09337e947844179d92df0874ed2232caaea0079bba932bb2369afb9a8ed2832c4
e0d537cc0aa4844da0eb89cd2aecb3dd959e4e33cc9a46aa8a7aaea199f4e99149ac50b1
a05cd20c970376cfaa5e61479dfc4f1fb4d39ba794f274965065a79536faa517
secret: 27d31fe80311249e1c8ae9bfb3d834a96486c91370595363b0e6f5d4236aea09
f8d78b2c712217fd5bb63c0e1c220ce8488df9d02991ddbd8b8e4340f19cdeeb
key: 30a72ea42ab066063c1a7fd99641ac76
base_nonce: 8d182b77260bd9e6bd2305d3
exporter_secret: d762b3b46ec8c4551ec2daad04153efaa9821707069af57a161fbb9
61e5cc0aed0e89dfa8e7ca06ee6d93757ac8744447f434c19d6efb0a926ba3fb77f471b7
a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 8d182b77260bd9e6bd2305d3
ciphertext: 4b455b6aef37f8692d8bf49ade5229d389db9d0e830669d5a7c6a746b6ee
aa18fa0569279e9868a19d2499637c

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 8d182b77260bd9e6bd2305d2
ciphertext: c1702ed997d8857b57e93b34c8a8155da168cd33583d57b34c56e46c63cd
8b5924d75666fa0709fac4cfb58dc0

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 8d182b77260bd9e6bd2305d1
ciphertext: 5b24d3042345607d39a9c2a1db55ea606281c6f1d9f09e9b9bede75e775a
03cee1cb6cd1eac6be19d8c9da3e99

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 8d182b77260bd9e6bd2305d7
ciphertext: e6fd63b63191201ee897a6f94b8d39cd30cff410682b1740e7841b4ae0e7
e49ae21d41b1bd52630388311ed922

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 8d182b77260bd9e6bd23052c
ciphertext: a06576ba21dad0a31a1bb5ea5fb5107acf3e4c99678da814f34f8759969a
11e76f27827820dea3f8a0f71a80a0

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 8d182b77260bd9e6bd2304d3
ciphertext: 22b68ad15ee5485eae80ec5c98df381cdc408e24817ca3e12721bd346734
f07e910edb46073a2a94b0ce9c4dc1
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
16f6a26d5af4d16364d25415569a69634aa712b9dbb47ec26b10a74fbfd31779

exporter_context: 00
L: 32
exported_value:
55d529a9cdd5670cf00179aad14c70b9453f4f46e12b43d2ab07db9f301842fd

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
a63161b41e23bb4cb3329af4a25fab4d6c4818f200e84fdb332f02df57c638b6
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 729bf523707d5e574aca2180a334ffeb5f56a3a8b326ca60225cc1389309978c
pkEm: 04074a6d306328719df46bc7ff5bcceb9c2084829132b4d2b2b1ae9a2e069ae568
67a1c748872af0fd179b11056968bdf9cef3ab43b07e92926f28207624574204
skEm: e43e5b4a68805ff5a06638d8cd895a06d9bfe1513acfe68d81052ae444f1da32
ikmR: 8578264010512322174ffa2528a697f4ed9d10335b9794b23bfbc464f60d70a9
pkRm: 041135938c8882b61de5ae7466b76d795bbb1490ab64ae79e86632ceb15026c9c6
2cf02fc523a48ed7bcd23b06c046b638bb15890698cd84569f72d3c8a8d18764
skRm: 3c91bc9a2541c205ded2a3fc7b558286dccec0aa01ed0ff7842b7a31a6ce0b61
ikmS: 157225ca14ab53875997e5f5bdd5bce4c714c631e4774d145313aa0f97ea46ef
pkSm: 04c9952edda21598d76a1348c327a43d13fc5ca1ce3c85d0fe2adebf867906b7cc
c404c909626f87128be720069e518ecfcaa4e355b1f47ede8cc443390f0792c9
skSm: f68d1d0b5c64933bcb4e70e59079f69f1b352c630dbb8d22e8e176c20c19f77f
enc: 04074a6d306328719df46bc7ff5bcceb9c2084829132b4d2b2b1ae9a2e069ae5686
7a1c748872af0fd179b11056968bdf9cef3ab43b07e92926f28207624574204
shared_secret:
c934fb34c38776491139e8773b9426290921d86cb88d501828893baf908e6ff5
key_schedule_context: 028bba5aff4a4a949c4caaf55df2daa905f5946efb46343832
6fb2dac8504145236cccff5a2a6115fd54f5fcb61614d951a1506b918aea54eda6f60967
8f4c506f0aa4844da0eb89cd2aecb3dd959e4e33cc9a46aa8a7aaea199f4e99149ac50b1
a05cd20c970376cfaa5e61479dfc4f1fb4d39ba794f274965065a79536faa517
secret: 98353fac2dae40ffa8265823561fe0357ef38e65b91de3b7798b6a6f71b7f728
7a430d15f140f187fe1722868daf26afc0795e57f7af5340a61be78edf99345a
key: 8168f3f41ba5c2a91680a52d3864e842
base_nonce: db0d76e9dd18e596db180b39
exporter_secret: 706cbf9128b9e0d2007f231b6ddef31799bf648abdda67b916c7788
5417c6362418ee1494799613088f5029509c1afbfcec32d269e4fae9d2fc8158966c9fa7
6
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: db0d76e9dd18e596db180b39
ciphertext: 0f06bc617f9ec9c96d862a83752dd6b9ff1320a85b4138354e159998db35
b1320a06c621a24eaea83f1fe43d59

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: db0d76e9dd18e596db180b38
ciphertext: c492d99c7f765306373c5355ffb684aa7c54b62782224eb1bf4f56d79011
b109dce53b0d917bccba6a46eb21ee

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: db0d76e9dd18e596db180b3b
ciphertext: 2307c1c71a8d09431d42a36ae2a01e162f1b286e7671fe94f8ad0b9604f4
32ec49e83ff45d99429e3735ceecc2

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: db0d76e9dd18e596db180b3d
ciphertext: af051a28b402ebe3fd48084def6482f7c987d459a796396a927be08c5d98
70f577e16234159b608727edf1d7a6

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: db0d76e9dd18e596db180bc6
ciphertext: 05793661de9dd2c9fd338f66c2d571b4480f3efe24f0dacea86634f4c328
7a2a4ac315d76d271e5f459ed15559

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: db0d76e9dd18e596db180a39
ciphertext: 18179e63bdbfa18511738fa89a4886d13fc5e6b710bd618662f85dee3e09
58547402d35696629e3c5c308fce3e
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
a29981c98fc41b7ae1bb0ce6795f966d833f4d1c6c16dc2fa8f885f1e622a75f

exporter_context: 00
L: 32
exported_value:
620e4a48a9144a534177c91724f0fe602ef5031d589a97486b71feaef3bb3e8e

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
75f73e0f68dec42a2c70913923cfe6e1cc07c2e8d3e4af4cf4c2ebaaeb5857c5
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: c77066b17070dcb73af19d0e52f94ee22f2e2da85f509b877d4a6bb2d9cfe742
pkEm: 041bdc639637ed1cb1ce00cce7093ac2bfc199c763fa8a9d76012ea6aa2230ffcd
5f2e26014dd1d18461fa3e8cb82511e7c804307c5d107b3a8cf392d65900f25f
skEm: 3040327029ad07bb6e246e3c1d8c93e2a7f286eee335ad8dac5cd761fa85f8b9
ikmR: 4f3df69eca2cd20da5068badaaca64393299d41435b7fb2c869327f350a9c33b
pkRm: 04205d8891d2234ff0656f0478bec3582e19e41b006e6eca94860735e4e8541d79
3ac37e4d7b71d7fe7e79ca8e41b8b0defb3d510e42abefaf25b6296ab2b6b5ad
skRm: 069a36056c439dbefc28e57e8db05bcdf2abab75cdc821fa2eb1e635632120fd
ikmS: 4f8d660d9aadc7f1d2eba192fd1510028b23626d96aa5d8e077fcb1248fd84ee
pkSm: 04c7fa4aa253ce2ddf9d9f48b170721f850bb7d111f6763c25207cac56f66d1a9c
a525dfcd3bba8c95c1077230868f8ab8a841a5caa8e52aa019be4ae54635344a
skSm: 61a57ae5362fccc2e2e49fad1f74fb3fb4513321115d087222c6be5ad89eb0c0
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 041bdc639637ed1cb1ce00cce7093ac2bfc199c763fa8a9d76012ea6aa2230ffcd5
f2e26014dd1d18461fa3e8cb82511e7c804307c5d107b3a8cf392d65900f25f
shared_secret:
889ed188ab8ba218fa0aae4dc2c674d1a338fda00364c117c89143a183137aaf
key_schedule_context: 03f37d94392114a83426ed4ef40b204fcabab8c86d1541b7dd
7f71d1b09337e947844179d92df0874ed2232caaea0079bba932bb2369afb9a8ed2832c4
e0d537cc0aa4844da0eb89cd2aecb3dd959e4e33cc9a46aa8a7aaea199f4e99149ac50b1
a05cd20c970376cfaa5e61479dfc4f1fb4d39ba794f274965065a79536faa517
secret: a4f50d164d17138e349c92e3ba4b11d5dddc8f82595f95f8e7b3a3a6291fa247
3543c92a8b55a60bb4c83030222a50fbed64cdcfc4ba40c3c97a7121ca3d064d
key: 7d069bc8de13d63e068ce2ffcae5eaea
base_nonce: cc061682cc7950fa3d95a6ab
exporter_secret: d584d697189c664ff6be2b9bdad061a47e0360b1f6243e07b64e34c
7098cf092a89e0c738180a19da9873a0c22909bf85e7c211ef0e2bd62770036c529dc069
f
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: cc061682cc7950fa3d95a6ab
ciphertext: 37ce5e9bf49f03584c1a5616a79c1974ee70ae7102b16d8938d61086a79a
fc93448cc17cb510d6bbc0cca4bdf3

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: cc061682cc7950fa3d95a6aa
ciphertext: 971bb5565b382c2e8b38afec66d1427b3793c14a574b38766e1ddb5abecb
e5b60500e0359b3663f6ba50161a7a

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: cc061682cc7950fa3d95a6a9
ciphertext: 4123081c123fcc76d72af6867738c9eb51df246bf56eaf2314e7201ea2ce
deb06823dcab77d99e0a7f5badad2b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: cc061682cc7950fa3d95a6af
ciphertext: 1a93014d03b16ec0ac0a00b2ddf7d883958d2dc007ff5f5e627926e4c3fc
1409b40166cdf2b8944c27cfb01bc1

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: cc061682cc7950fa3d95a654
ciphertext: 2afcacc3f92b189bbd050b2e07e82851d69c56bdb32cdd5ca409ef3e83fb
96c2772e2ea08e9cbe9b69232e06a4

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: cc061682cc7950fa3d95a7ab
ciphertext: 8093f61a1ed70c9b0657313db0e949519d560d4b9cf47d46d3d1426fcea4
aa0fe9926d913d8d75ae05ed496077
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
a03ce90958dea682f1e74bddb8c5531729a647dc363ec01214e59243f631b095

exporter_context: 00
L: 32
exported_value:
6e1f2ca1924ce2f28490f0ab61ec2d8b66ba0f05ff0a355428c82c8888c090bf

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
e48cf1562dd1047c3138f11ac074727f807b8c55cd3a48d63906aac03a6757e5
~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 1c7ea2dd703c3a98678dcb4a0c75029c803bcddd7f045c497e5ad2f6120c006d
pkEm: 04115d2cc2e317e363c2884f3f850f99e1292a1c0fb5c768f18096858a1fbf0ee1
d573f3a6a40543207094ad89a2e1f87a1dc46bc98638e635dc2aefd40275d1d2
skEm: a4f41913f40f3d78562311e8b32cf26152731f7393f0219036302e59e3e8affa
ikmR: fa73e26ec21d46f603dc79eef82c023a738fe93e4bd559fa84d154887f05d117
pkRm: 0494eb40a3754f10995ab4fa52871d23731e551c401fdac3fe91ad502224148300
6830de6232df192e003f08103bb7a8f62af6ba115fcc9b993afd939337b5d1f5
skRm: ce56f433ee00c982a7f3c32c537de5af083ab467d662215e18b2deafb2e3750c
enc: 04115d2cc2e317e363c2884f3f850f99e1292a1c0fb5c768f18096858a1fbf0ee1d
573f3a6a40543207094ad89a2e1f87a1dc46bc98638e635dc2aefd40275d1d2
shared_secret:
992458cc139e5ae3cff92f7916454be0aea2effbcf455991db991671436d9854
key_schedule_context: 00f1c18fd8da4af5b3ba4b18ab1b66fc11804d8e56de307dcc
375c6c528520c91eec1f66cc97b192a4dbe73c73fbbd95df11beb60644bac645bdb003f9
3eae1438
secret: 1603d091f8c0ba27376622826a61479bbc6e266b52898a269fb0e399a23c36d5
key: 40fb9b449fb4d8dafb435125bac1574b3321f51441492fd286f325b0db2bcbd6
base_nonce: c4341b77afe0f43c618a8edc
exporter_secret:
3f54879c6b015df5d6887d1326edd7dc5861789a51dbce7e74a7135eb738e50f
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c4341b77afe0f43c618a8edc
ciphertext: 393e3090eb0b369f5ea3e0ea7dc981e0b8336d3b3e3d1def5d9501f3e32e
f00826d4ca4b626341a1eaf0f4ce3e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c4341b77afe0f43c618a8edd
ciphertext: 9a9960994ae5b16e588cdd1c8dde16fd80b5065fd499ffb29356e0893b75
ea0bd470874bbf75ce2ae8caffa590

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c4341b77afe0f43c618a8ede
ciphertext: 0c7ac0e674d28ff5ffe867c846a9897128aae26ef9c4ab92013dc581f009
08efe69e4eaa8eea11d9a7c966ec1f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c4341b77afe0f43c618a8ed8
ciphertext: 6cffcd0e2b46d74f8c8547c73e6112157b514e236a3b74d44cba8df219e7
84dbbbf22e98e4177ae2d867fb86b3

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: c4341b77afe0f43c618a8e23
ciphertext: 223c7fcda08551ce2162422ec833d00bd5f25a56de9d2242de63365a7c9d
0cab90e847cc2c0450b12ad3ae6989

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: c4341b77afe0f43c618a8fdc
ciphertext: b3aa3be16c072da3aa06a850438bbe0895a51aea6bc0a3e5228c19915c4e
ac73aaf9df028bfbebb4ec0f899405
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
3e580133b27fc552e7229a5f0891ba1ee2297d4338c3f7fc2d36735c65bbea1e

exporter_context: 00
L: 32
exported_value:
145399af8fc0191326b81a8062a48c2b6d897c947e24043e1b24adf730d62c4b

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
8c457c5c614c15aee373f5ee78e1e983b7a20ceec3717e49c3986ed1789da577
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 26f07846c6436ac9e1f9fc3dd0b815308f59bce72142cbfb770c31d1a5ec0f72
pkEm: 04596cb40b1b29dd2612c9511c0704d475fedd641362b3a21ee92188cccc41d454
c77e209b828f0faba98ac5781a38e4694d6bd872da1f796f770750f6e89166e1
skEm: df8264f39aaa49d217201250483ecac8a91e3d93fb05ba6340beb470189d7dd7
ikmR: 86634f92d35c41ddfdfbbfef1f7cc871ac2fa40d5710f1f33ef2fbe8209b7660
pkRm: 0468416621586e3f9d55b277e4205472b04a33173f366b946d5e2b61242220b89c
d91076873158dc0424232fc9b181c850480a54c54380a39434735d60d9a6051c
skRm: 6a000c019a2fe5d300da437988c930b1c16b454aacb5cc909c7dbb4a47c87734
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04596cb40b1b29dd2612c9511c0704d475fedd641362b3a21ee92188cccc41d454c
77e209b828f0faba98ac5781a38e4694d6bd872da1f796f770750f6e89166e1
shared_secret:
695216faf075dbf9e819b3115076a769ca4e087b978940c974e3e2ad4963e472
key_schedule_context: 01eb05e31a1def4df3a3750746823861cf1546335001189fe2
870b59b88ab18eb9ec1f66cc97b192a4dbe73c73fbbd95df11beb60644bac645bdb003f9
3eae1438
secret: d145d15200d2f6d7fd923ce9b5a0dab2817c5c8be868f1f2e9aba8eee0c6c766
key: f03ecda0fe9dcdf6677afe4d0c5b63317c539fad44cf467000f13121fd56ec1f
base_nonce: 4cbde1b60ff66f9fba5514da
exporter_secret:
d85015754a4581003a3b835b08eab687a782862b4a3ded3d1e82c9eaccb3f28e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 4cbde1b60ff66f9fba5514da
ciphertext: 317900d5594ac44c0fb670dc6943ede71dbb227aa00274adac242e65b6e1
a4e4ed67d13d03fcb1911e78de5cd4

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 4cbde1b60ff66f9fba5514db
ciphertext: b2780f4a3f13c64aad7a519b7a239c3fa510caf61f400a4e9cb7623ca43a
1fb9d9e4006c2661b91e494b7c7d1d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 4cbde1b60ff66f9fba5514d8
ciphertext: e774243ac0d83ee556563f8c790054219d19c974ce4d9265cd4bd8d0303f
ae0ff88c7443e6fb02298b1334cb0b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 4cbde1b60ff66f9fba5514de
ciphertext: 9605698d1fec0bb2b3b85ef6caa51ceb8df31a0399a24bc3679c1b4b2fbc
bbf9f684f822e0eb2782375ce951f2

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 4cbde1b60ff66f9fba551425
ciphertext: 0780af9e129d67a61073078b62d2e75b2f94b765dfa1c66046f0794ede3b
a7b5d637ce8cc3571c65d34740eb33

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 4cbde1b60ff66f9fba5515da
ciphertext: 48907dcbaade5de1238d05751c700f5971b79b1615f8b9e15baf282e0878
ac081363e20171156c72b844fe44fa
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
18bfe65f86a68a2eabfd4cb674239f5bffb3a1f3fed95a368124850842707e65

exporter_context: 00
L: 32
exported_value:
24822d24aa1cd4947f463d43ad33c611278d7fd20bce5ac5b01374d7851d0a31

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
19db4d73cc5ab16705ceb5e18d89f4091d0d0621209e6034f71c66d5f6830196
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 82c9f7cdc3d55b5523d1eef476e3438d2e5dd910d13b17308f53fc61ac93c2a8
pkEm: 04a382ed93de16e67c3c68876d3b5d10c54f87629d32cb4098938cfb69b79a4e39
a47e376458d7c42a41f0a06a0a137c0550212b8c67e2a9c6ad863af4d6288f7e
skEm: 4f908a50f69dff2a769a3f223b859242f9b293f96e138f564c67517a939671f6
ikmR: 8f48a15aa6f9a1b15b7c8d2064140364a1a61ce6fd5dfd6a1fa7d94f09882787
pkRm: 04ce41ebe6d8931e4252adae4a792355510b73fedb04c58c779828763ab63d83fc
2ec6eb22359c36da0d3daa654f72cb79e81fcc8345d36285aefb66b9094549c0
skRm: c4946c90738ad3336d2c7c94e3e58743d156225e742d5ca0b1f995eaad82d92e
ikmS: c65c7e9d5913816dfe0f5246ef876fd69ab045e88256eeaac1d16e810a4ee1d0
pkSm: 04077d4a2b05263599f893ba492554bb325ad471498db672d0bacdfa74e1d6097f
a663947874759514545ed00f38c496f78a28ba574cc51710adaa8356b6d4beda
skSm: a29e05133a4d4b52df2b8d33798dee8be48f79bf63daf3ec9579df40fb6f704a
enc: 04a382ed93de16e67c3c68876d3b5d10c54f87629d32cb4098938cfb69b79a4e39a
47e376458d7c42a41f0a06a0a137c0550212b8c67e2a9c6ad863af4d6288f7e
shared_secret:
0cb8e6087fc5a8679347f5700411d40dceb6983f620cc25ca680bfab7c25ac2d
key_schedule_context: 02f1c18fd8da4af5b3ba4b18ab1b66fc11804d8e56de307dcc
375c6c528520c91eec1f66cc97b192a4dbe73c73fbbd95df11beb60644bac645bdb003f9
3eae1438
secret: 170ba1cba1890983dd4f8bdb136dc8d8a80db0c6cdc42150090ef8b51e365ce4
key: ea8b805ac458810c7b9dc316b1e84f7531c26b765ffb5b6eb0e08adb5f020e26
base_nonce: 1c6dba370cf5af89cdcf0ef9
exporter_secret:
a1eef29eab08f7774c2119b03f5d6e79ae734d5c42830e2dad16461efdf51fb4
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 1c6dba370cf5af89cdcf0ef9
ciphertext: 9deb6199c98fd6fae9d791d16be10e9870cb1dec1d5aed58ed60c9053ae0
e23f14b7f45d1f9d7b66f5ef4cd18d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 1c6dba370cf5af89cdcf0ef8
ciphertext: fe2de76cf1763e0785164fae9618984922eb9aedcf5f03d060ea87998150
140339ddb5209d972ca709dc2a1d8f

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 1c6dba370cf5af89cdcf0efb
ciphertext: 16a2b8119c4695e8ad2f6dd59470071c390c4666a44e55f58abade397ff2
a4b71258c0efab257cf50cbdbb51d1

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 1c6dba370cf5af89cdcf0efd
ciphertext: 0b198300565c245bde451cc9224d2337532613b4254b3120796c5c5726e2
92f7e23d2641a5c2d7f96358febfec

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 1c6dba370cf5af89cdcf0e06
ciphertext: 4f14b12b4eb93e63c23a436f42066e9a1f69a6d200acbd79463d622a4633
8a8ad25e85b2bcc6766aaf12be0b56

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 1c6dba370cf5af89cdcf0ff9
ciphertext: f77682b845648b450b9e1ecc922020abf92e4deb88c57e9ffaa9137a8100
40c4f3e84edc49a9a98a70561a2bbd
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
bf435fa4b29e4c40dc253dcacb7d346c8ec5deef4eb3d724fc29df1cbb54321f

exporter_context: 00
L: 32
exported_value:
0f756e3317dcd06d8edfdd466d09555647fb2a5d97222309677a87c73d66cb25

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
cafbc83f4431d0a1aa3769ea61a19f25025fe9f022dda5dfbc621e786a73b449
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: d25ae0f5772d29c7631b3e6fbeddbd5ea3480cfcdedf52b62ea53a78eada0b51
pkEm: 04522b87fef8597fb474df8bffbb338bb4aa7870ca1a9ca00b7280933110559cc9
0985ac90c68af10c5ec2a8a7602e0d124efec764808917dcea31a44a7ed7d887
skEm: 491a0cbcdde5a45ae7e5b5008214d138274a38810177aaec36c1c7ee8a926443
ikmR: 991577662e9bed488a7152b4994e212806919d1c685ac81b2c83bc307c835f98
pkRm: 049da19c2e909d90ed12c59fd476bc49283cf2efc99088171603d83801aa8f762f
6ac7d66d333d4c43b5489e92dcb0a11c59efd5729ae633f96da99fc073ef32fc
skRm: 0c2e886e11eef8d6858d5745089b8c48441edcfe1db4bb6fecffd8d729dd8f5d
ikmS: 330f1e1338cfb63cd4fb94f5f315da37d71e89350446b2510e76d2dfa8568181
pkSm: 048e36f8faa39be80d56ab8db82fb29c66c6a0507efe6e16385ad3269c88476048
e9d905fe5b930f8e84a9dc4f8a39e19971273515e4a29d762fa721d26b5fc771
skSm: 415c85bd71e31f84b98a283b7aadd1ba5ceadc024657801c0d5208b28f97072d
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04522b87fef8597fb474df8bffbb338bb4aa7870ca1a9ca00b7280933110559cc90
985ac90c68af10c5ec2a8a7602e0d124efec764808917dcea31a44a7ed7d887
shared_secret:
f8ac47019149b291838334655c301df8a4fbe457fcb384ca7fc3da561ec24ba6
key_schedule_context: 03eb05e31a1def4df3a3750746823861cf1546335001189fe2
870b59b88ab18eb9ec1f66cc97b192a4dbe73c73fbbd95df11beb60644bac645bdb003f9
3eae1438
secret: 7cb3f10b577b9aa168c43cac9cc892ee08a84ad07ee10c29d401924324e31c3b
key: cb923fa29319dbd29c8eb0e3f508140c55b1abab7358f8a7cfa90fe636849e27
base_nonce: 2d0c3bef72040774293c586b
exporter_secret:
d7a2c747836c0d76542c98535c4268767bdfb8fdf5b4cdd452cb0affa2013a45
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 2d0c3bef72040774293c586b
ciphertext: 0a0a68b3cdc8c4cc5129c2db2d5e66062757b5ef7c50e72b3df94baffcde
b1e9ccab54a48357b68d339508e07e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 2d0c3bef72040774293c586a
ciphertext: 60207e04871f4a3327ea7079b217700b24db58632ad208476d4a83e3bca6
c3d68060c1a4336bf36f34ecc608db

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 2d0c3bef72040774293c5869
ciphertext: 35f45af0971268fdd8fa8c41780ad734140917a712e3eace6daad62852be
1ba1c687d53250ee1db700f2269fa7

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 2d0c3bef72040774293c586f
ciphertext: 0e77d22a859a074cc6f2bad3a5e419e3d1ba5fd06e1dbc7283878f5e07b6
41a7877616dc6d07120ec6f9fc834e

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 2d0c3bef72040774293c5894
ciphertext: d773082e101266a4757ad6ec18b11734e9cb70f6165734bdce3c02253403
7839afecd838cb82f89613a9c29609

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 2d0c3bef72040774293c596b
ciphertext: 2c57d926e3d696b2c7f1b8b5bc04a76038a94901d321dd62100e48655073
d600a9eb61305c7c421a1af5981022
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
3f9a976e3eb099fdc6ea1a97dd2418209d76249ba32abf5698a6444277f75bae

exporter_context: 00
L: 32
exported_value:
45f006575c8c415c8b6bb4c4520f9c4975feb24bc2ea544530bd15509f38869a

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
a8db571cc01acc0b157efb86abc4d02a53a11f2f5adf125b588cb2d29a92f169
~~~

## DHKEM(P-521, HKDF-SHA512), HKDF-SHA512, AES-256-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: ea39fec1941c5f516e19533f40d415c65fde023c10c559f3845e71ffccea478101
573d069cc67874d5b2aba6a22eb51cdd689836b7e9cabbb4469c57947db7316fa7
pkEm: 040197302e6c03e86ca3d9aa27ccd387944acc362099711a96b874f7bb07eaf770
a0e11228441d184aff4be0916184f2b38779b9127b5edb9c8046f7b558d75fffefea01dd
5754fc8c82b4076558d53fb2f3e60fd1f809d2bc9d304c2d3f35e28ae7757d5129295c94
bbfe1ef2d01a459ecb7a361a8ae43a3d38e41d01b466f73ebef26ab7
skEm: 01ba7db044a52f3586a59e3f8c2953cc7f45a044a1389abddfac481c2354899bd4
370807345e5c04e35e0fff0ef755f209fa6cb6f5f63917f37ca140a001bd2bc6b2
ikmR: 8249fd42416aba5b0d51dcd3548d774ae172148cbba1519107c5d84a160225441a
9c018fdf3b9ffc2c41c1c62e29208d5165a59e7f14fe93b4f911cbbebda1904391
pkRm: 04003aefb3330e704d6c22ce7b67bab9b0e404be7f1374d0e6d3feeadc57f6b203
1c5669516a8cbc309e895c6634fcfe95039a4648fc093f5bdad77756b363073d80c10051
63c6fbea2c8268bebf70c6ca79928938d3e8d71471b1f116c1f3d23930e361219b7e104d
3a76b7377f18a84abdbc84a41ddc9a83d6b6e7c55887a95fc66a6137
skRm: 00c0c8e2de2efc6aa11f3420cdc1c6cba2c44d79ccf1c89d86b16090fa05247454
d3808b5133ddb923a8bfb35704f5d3c210f3ecf8afe8235b0cb4aaa38eff05f17d
enc: 040197302e6c03e86ca3d9aa27ccd387944acc362099711a96b874f7bb07eaf770a
0e11228441d184aff4be0916184f2b38779b9127b5edb9c8046f7b558d75fffefea01dd5
754fc8c82b4076558d53fb2f3e60fd1f809d2bc9d304c2d3f35e28ae7757d5129295c94b
bfe1ef2d01a459ecb7a361a8ae43a3d38e41d01b466f73ebef26ab7
shared_secret: 86af77da36582559e432f71964d74e7bbe972d8a13dd2bdf8375672d4
fe446d75c6b5f82694f45aecad75cd8d5ef0ef91ccfcfd0228691087c66b5ef75384e27
key_schedule_context: 00da5a1a3c5b8143e6db5a30d288a2ce1eba163576d754f4cb
c4ee43552ebf7dd475cdc5d45d9277ff3f7d2edcc13bd6c17f5a87fd01740e4f9d336aeb
b64be9f73b4b7a4cf3d95651612d822dde9365526adc78d0a7d77e570fbf3067ea90b138
e491d673d8666d8e312fc9b576111f058a7678a2ecfbcb0b9c509f3c3707875f
secret: 80a375f439f5f6f3596cc7e9f10f3c864d93d8984186183675aa66917bfc990d
6a3777ccbc800c3c72c0334b08746bcb51ad076ba61a6990af5999fc1031356e
key: 780b67de89a3c702fc30c5f159f25292c0e2f16560ea9c6b4b6183fd542c094e
base_nonce: cf6470b12bbea9f9ecc1fa7e
exporter_secret: 82a365c4c7bc1d11e2c43aae232b23f709abce3bae7e70c0c48cf6f
73dcf31655a466cf64a5ebb059196a7cf28996f050b8b9990480a44d5ece8e02e76b4340
a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: cf6470b12bbea9f9ecc1fa7e
ciphertext: 173900910caf7c88867dfa2a67ef51b092246818ff889f1f7652cfa7ba6f
f46e14657d491c8276fb0518521b98

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: cf6470b12bbea9f9ecc1fa7f
ciphertext: dcd904b4b5f6f28c7a2f6df76feddf873a9d50df9ce80414088f5a2f5774
072ae262a4d022eb70e5fbe78aa3aa

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: cf6470b12bbea9f9ecc1fa7c
ciphertext: b20313aa367924629b7bb987dc7fe773b423e679a6a95ef9fc0bee22c92e
e2e6ca5df41038f42ab2b04ae141f5

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: cf6470b12bbea9f9ecc1fa7a
ciphertext: f2d5f28f1325df43b603bf58587daa38d3843972582e5d8f8e07570b0c86
1324b58b2a1f14460f2382defc3a1b

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: cf6470b12bbea9f9ecc1fa81
ciphertext: 14e55d0f6aa6ab051c2e14718a3a967c98c0e0621e3c88dd378aced3bb93
84f0d30d6372f59ae9f06eb9e752e3

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: cf6470b12bbea9f9ecc1fb7e
ciphertext: 93ceee2ac547e0adb129be803b88540c09b63c1885a7deaadac421b24339
e5b1ed4b808cd6af9bfd9770ae3c31
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
bdb9c5c4783ae29aa24dc38b6b8f65e798cdbc406c2625458d0af113e2082186

exporter_context: 00
L: 32
exported_value:
a1740f5e40a73fa65afe3de3257731e361e373cd329f9d8737f9c2c136829345

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
f375c057106cb17acc1c32fab4e53ed03b96df53880b9b85539629e82e21ba8c
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: b563555965facaa37a5e754cf2e50193953e1d527e61637e521df1868354799258
f0d15d8807750cea08e9b6a358d2440ab06725861b237fb69973cf41e802434433
pkEm: 0400761083a4d901be728ba30c9d2bc1efb73a022dc1d177a1dadc1b8395a44073
bc8e7988ff43e7f50f320f06c4bfa6b2cdb4c103678cc829b3ab0f80fe407283420300bb
3c9150e880b55207ce8205ec56bd3cf888b89fa17ecd760785706928dfe18d64f2a5f4b3
dca1dab32289a420c24d1cbbe58ef53d1435cd0b6f77fa633f8e76aa
skEm: 01d319414b6313fafd44e4f3a30f923344b9ed784ec26b97c6653a290ce9f2ad3a
1c4f6331966b9c8d69855b39df1fa994abee346de26fdca5834a2b5df0a7b18a38
ikmR: 2be954cd856c0c548ec6de490c821be20c4fc9610b5dba1831c698045fa01dbceb
49f8324bae26e5d1ee62db3246d65492812e2c539b96bc580d46c247304adfc55e
pkRm: 040035d455bcf95a7c9d492dc4ba04110435706a6fe6e53fb5aacdb624a03ce9cf
ebae3cbad679615ce00dd455b78a3b7de5d891f4ce4f6832c5ec190dec97a31a79650150
00e29189dd08b1058d5d66fa995b068022781c6ea7ec16dfc2d33891ebecaadb17003dcc
e0f6bdc6fe6d7c4d0cd912c536c1f69d08faf6e7f299b0ffc2057c87
skRm: 009a5e4535cca836dde84fecc03d4f2efe7045bb79c43a9d995845fd2386bfec8a
c415fa35ebbf5e26617bf7fb6b789f2cc086c1075df94868f84a9cd90b48195348
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0400761083a4d901be728ba30c9d2bc1efb73a022dc1d177a1dadc1b8395a44073b
c8e7988ff43e7f50f320f06c4bfa6b2cdb4c103678cc829b3ab0f80fe407283420300bb3
c9150e880b55207ce8205ec56bd3cf888b89fa17ecd760785706928dfe18d64f2a5f4b3d
ca1dab32289a420c24d1cbbe58ef53d1435cd0b6f77fa633f8e76aa
shared_secret: fed1702d573f7331a30173abc5f7f536763159391c71cabd6ee368105
1a8b0c4f8213ae78b920f9e33f880a4e3a717180274d86340438bd0a3e25eaee3ea8c92
key_schedule_context: 010fd8cefea7dbcb4870549c1d9aa61cc82348ba99f41333bb
3688fad192a16d85283c8d5041a16ed08480f03dee01579b9f0e2bb7104cc36fce2d8bee
39bc20f63b4b7a4cf3d95651612d822dde9365526adc78d0a7d77e570fbf3067ea90b138
e491d673d8666d8e312fc9b576111f058a7678a2ecfbcb0b9c509f3c3707875f
secret: f79e77d8b118c984d7e178073c3a1c385b5cbe18b737b93ce54c8979ff84c5e9
c095b37b93530433c75dfac7db9b9b6489e6aad0bf411f0d05ef272389d9ca3d
key: 030217f89b8673d7702c8698cf7e1eddaf1ad4b5c457c9f4888d8d22bd3816c7
base_nonce: 826086111c4d7b535e35b56f
exporter_secret: f747a66e44d7de00c8486f04d3a0d37f3f43c2c0d7355a7810c9eea
7b16eec36d3c1e590dc2c48f024ac2c2dc2418c7fa901c2b1ce1903d230986f5b04745fe
3
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 826086111c4d7b535e35b56f
ciphertext: ff0bdaa192f9d3c9b2456bf17f1a4f5e558f1925ea96112d6c8c388bcdff
a54c7554dbe809bcaac4aa36681572

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 826086111c4d7b535e35b56e
ciphertext: 48662931e6d079c8e23d36318adef8025feef6d218cc99f80e234fb28b2a
d55975d1ce8a731b70b4b1e6c5d31b

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 826086111c4d7b535e35b56d
ciphertext: 0d0b49d991a0303bbc36cec1318e7276d6e9d9bd9fccf0e7474934636562
35fc23fc724a6b3e55f95510638ce5

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 826086111c4d7b535e35b56b
ciphertext: 6734836f67a84edb6262747242c88bfd6c7dbef60393a0480d297a83a22d
da51f3fed7d531cd83315e833bf8df

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 826086111c4d7b535e35b590
ciphertext: d7e4aa09cdb5db8b9ff206b747645263ee14c72d9b5f99f6e5fbcb0d8b88
eb9fa053702a1f2d977ed76db2cf74

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 826086111c4d7b535e35b46f
ciphertext: a0370c07b913dd731b8dc342beb13a89f29c017bfc6618c16ba1cdbb6092
cc305852c96d6324e4ba128335bc5a
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
b07b939766998971abe37fcdf96d868c97675049ca2656d464b12c71d79712f6

exporter_context: 00
L: 32
exported_value:
8ec328319c37142becb6620c8b5a7ee7cf090e8964dd13f869d08f78c00db889

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
18b05591dafe354b5b4e3db924f4f8f4a6d433890722b5b85fca83391286da60
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: c9621b9ef899275dc970606a2b0806fe860f62d539f3ee618a9409009b8ae154bc
4acf495dd9fa8f850c4dca82b923b42270d7b16ed343c7e86e3036c88d0d7d77ee
pkEm: 04005b8909175cbc8e7e8e94d0d8c6e5079d53da3ff6489e2ecea431e14747321d
ff54548f3b89842a2a0cbb326aa7537a5747464de79a4e71411cdbc06f439852a3f001a2
2941e560fe64ef80ac36ff28b1df51070e5c59585008e4e4a724915b88c011cf7493b915
f53c705fbcd461e0cfad34b09e74f1e201bddc6a95284c7a41f5b84c
skEm: 015f1715cb1d849065d403e0d3cb3ba7bd083ccf59b23ff8f289b4aa11c0d060d6
b7f22eda773e490fdd4ef76d6a0e48a5947f3e3a2c2952cef15337444c0e1a36b3
ikmR: ef805c20cda1fa06e06cfb968ad68c748a3dd94337f7357ca0060a382a84fa5de6
df3e3216f886957694547264d5bc63450cfdcc4d2b33fc8ebf8d7c708f8b5e4bb5
pkRm: 0400c171be51c683af5ff8eb5a0e03c907a6f6e14d8314a4f81733ddd6055b8c81
26f50b539f7b825356ae96d638f357122739c950f80ce5d7ed0a65bad442b66b38770111
861d3ba2d5d57c0f5064e7b60781d38785f04ae767840cb764bf854b0d411337c9e4e415
b3491a97c1a2555bac39e2910ce0e010379929ac3e0d2938c8baf6ca
skRm: 00e7212fe01bf83edba622ed8c317db92cb3901a0c2584cf6ac0d2878453a4394b
15656df990913eefc87dd88fbf54c4aa2e04fc9b19712f84277cc2e27395eccecf
ikmS: d8779e14425887ebb21b1952b1a0b77842830aef910724b082807dfebc8ec309b4
969da762369e77834593970215b85510c9a0347ff14c8583aae7c9c2208275b740
pkSm: 04010400b58ba4680c7bca0d634efa7dda9a74ee1cd90bce25ced4eea703c558ea
b6f196236230eb420c41c8cef7d9466c7d0689f31031bd2451e959eadea9cd5161ac0088
6db94d8cc001caca6ee8003ed5b9885e657a7f41e79e5e53b42a5fb7f5dad9e7a871797e
6f070bdf1ecdfc2f8660bbf0b2048f34ac4c51a818134eeb153b552d
skSm: 00bad304cf8e460014c92a20e122949f4a617f23a9dbf370c85972121e6445a5e6
d81c633cc7c33a015ad4d09473f0d0c05f3d1bbe73d5d5824298038ed12ace3fb1
enc: 04005b8909175cbc8e7e8e94d0d8c6e5079d53da3ff6489e2ecea431e14747321df
f54548f3b89842a2a0cbb326aa7537a5747464de79a4e71411cdbc06f439852a3f001a22
941e560fe64ef80ac36ff28b1df51070e5c59585008e4e4a724915b88c011cf7493b915f
53c705fbcd461e0cfad34b09e74f1e201bddc6a95284c7a41f5b84c
shared_secret: 8dbc4f750e506eed8271d6c48efc8a65981bb40bb9215907429ecb396
e8ac19efc5e1c22c26191391e6782552e2e84b62998ed9577eab755c03d12c3f221009c
key_schedule_context: 02da5a1a3c5b8143e6db5a30d288a2ce1eba163576d754f4cb
c4ee43552ebf7dd475cdc5d45d9277ff3f7d2edcc13bd6c17f5a87fd01740e4f9d336aeb
b64be9f73b4b7a4cf3d95651612d822dde9365526adc78d0a7d77e570fbf3067ea90b138
e491d673d8666d8e312fc9b576111f058a7678a2ecfbcb0b9c509f3c3707875f
secret: 9684d096debdf231690f99b7db15b7ad60a7feafad670dfa0806845dd462782f
655f51e5e5fffcc3cec6d39439ebbd898f10fb93cea7bc88ccb9ea8f5f2ef082
key: 6a2322915597c63a3dfd1acb98e095aa7b0b43d7b6113f0009b1518daeeab81f
base_nonce: 18ebf5c7e04f885a4e7cdd79
exporter_secret: 85aeb64ee2265bc1f9b2fe3fcfb94adab727c7729b5f2bb526045e9
5f11ae9834d08f81e59ec4fb6cc0112dce1e0e029b1ff60082af01f463e469a9268284cf
1
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 18ebf5c7e04f885a4e7cdd79
ciphertext: 6b15afafb3221c5bcb5388e00a844385147163317d4180dbd30570689f74
bebc08000124a63bd6245385cd398a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 18ebf5c7e04f885a4e7cdd78
ciphertext: f6940d2fea5b3fb27f64b61319d57296c14b6612244a6d9df969d33f6d68
ff6740541ffd29aaad815640f2f4b4

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 18ebf5c7e04f885a4e7cdd7b
ciphertext: bb40476001f11ca66c75ec2a6755ec96a53f24becaa6d1135073369fcb13
21c10222956e1186148ecaf9349bc3

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 18ebf5c7e04f885a4e7cdd7d
ciphertext: 2aebad36cbe3c6b0eee74a0fa9f68040680ff0c7ff5600b6854c13c3a316
581722a56c566d633aeebb9946939a

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 18ebf5c7e04f885a4e7cdd86
ciphertext: e05a8eee88748cdd53d37cc79778afa28609b491aef446faa0fdb923ca35
5e3236c4eaa570b9ff373399487fc6

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 18ebf5c7e04f885a4e7cdc79
ciphertext: 7e5cefb4a94f4b70e3bd35f6ff3f638bd0364d2e93acc8a167a7a67f29c2
8848318ea85c8288bc0f2d31ad910e
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
d174923ac520b8cf125e9b43d2c30fda710362b9dc3cc2d37f6d7838bfe7ce18

exporter_context: 00
L: 32
exported_value:
ea8b6a12c7e6660722548ed750825feac6f215934e06ff3381a456e017239b44

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
164c91035f1d5fbef901eabebfa4890e8e7ddad325e9786b149deb26a16f65ec
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: d7537fd470c0beece615e26dd109922460292e973127cb4e22da16c0756fc33622
4e07dbecdf36edd144ebcd82aece3db52f814a33a639b5e7c964b27f6e3195cd73
pkEm: 04013c31cd06bce15d1b463800639a69d289d76144c1426f9061f4b0245b8490d4
8e29ecb8b3f2165970f341544a50d6017957e5c3f09b71f0a3b56af12383a53fbd9200b1
d5c6833a5095d97982d2e3528b38e4664bf29a719beeb3bb2b7e5c4e2acb3f0bc1387eaf
a7048e5718a27b6d7e25ca4b7e750386cde8d89e52c39f98db734671
skEm: 01129211d633b2e9593d1512f890bb8256e748cc6a45f75162d1936763957b3882
306f2dec7b70a8f6f46a70ca0bb1b3a4037fb4308661f45c56f04ff027c8721f6c
ikmR: f0858f5e1865db4fe45dc3274bcd273a29088d80f9203a16ec1210e3d81dd50a99
f15c427d547fea55593e2ef834beb5f80c536fdd2881a8943c05488a371a3c988d
pkRm: 0401c45cce1bda6afdefd49a12d9fc2d091f89e87e6d7932023342ce78d87e564a
0ca371795554d687a0d5d5982df2ab507091f0ffa70235710ebdc19db8968876d7ed00d4
051e3d606e88886c97de770fbc6270978d71c6b7a374f2cde4f66c776678799991cb35e0
9000b2b001bf035a1aa67f18d551c0d2c7a8a7a8e38956325c775892
skRm: 012dab66607b30642ecc1314f5345a595826c3c04432ae9a7f8fec1ca7ee71687d
b7b120f123e7f21f5326e5a379f78d8f1af3c971a1407f66632e68b23c75b28b1a
ikmS: 1e8d0026273feb61537181872e03ed2c7756f0ed1c4bb9ecd159614c2afdcaacc5
fcf70f6d30d7ea6760c98a1ce1138a82497eb72461ca5da50c8729d431de53857f
pkSm: 04000890a9d2ef896c4c307b4e8c6e56639b68d442309e8a67ebdd80108b4bf350
1b30c341a119b61bba2d17fa5a61f570be6ccc0f930057c1fa51050830e932eb2c3a006e
1b2e05fc108b4851df60235fe387ae441c74df048e7a4c31e93f4ef3f44ecd2e7aeaf34f
03db68a91e5cc7862a35aa4e6503cd40ac4456ea5b0c21e1fb00e26a
skSm: 011e4054db844866d6e99c6973972ba646842cc1b19cfcfceb3b5175dce007ec5e
36e3f9a6e63e06615c6f1b6f983022040a00f64428bc9107f6e3e370d33f158de2
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04013c31cd06bce15d1b463800639a69d289d76144c1426f9061f4b0245b8490d48
e29ecb8b3f2165970f341544a50d6017957e5c3f09b71f0a3b56af12383a53fbd9200b1d
5c6833a5095d97982d2e3528b38e4664bf29a719beeb3bb2b7e5c4e2acb3f0bc1387eafa
7048e5718a27b6d7e25ca4b7e750386cde8d89e52c39f98db734671
shared_secret: 0f942166336ecbb2ccaed99d7b9573fffdb7da9b8c1c68000d0fcfbc3
39c86e826f1d80eac229fa924990d465136734dd94ff5ac53d95ce0955c527a35d47151
key_schedule_context: 030fd8cefea7dbcb4870549c1d9aa61cc82348ba99f41333bb
3688fad192a16d85283c8d5041a16ed08480f03dee01579b9f0e2bb7104cc36fce2d8bee
39bc20f63b4b7a4cf3d95651612d822dde9365526adc78d0a7d77e570fbf3067ea90b138
e491d673d8666d8e312fc9b576111f058a7678a2ecfbcb0b9c509f3c3707875f
secret: 5262f5c006ae9f942ba4326c683cac0d3885fe4e97a4bc4445ed5975a50ad696
a20ed2adfdcd9b3d83f1909e8e3f6fcb7501e4e3debcac274959f243575a5a5a
key: efdc16c82ea9dd9761b6379e11e78c87931700e1f6714dc8c24019ff083e3c98
base_nonce: 506b1a27c322908a696ff219
exporter_secret: 702d2ed8e95bd3d75202950a39ff26a7cf24b4f6bbd9556646992c7
770b3c8d74fb8e82fe6da5518ce364ac3cd0a93cf15ccc86cc6f18af420a62ad8c06cd9c
1
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 506b1a27c322908a696ff219
ciphertext: f287e90cccad8b3d74098f52c837b528711e45b1b908276c53227742f560
820f5f92bfc4b52bc9a0201d65f7fc

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 506b1a27c322908a696ff218
ciphertext: fa030f97ebb74d8693217f1f71951d8945116b8363ab2ee7eeaa7483747d
183bf87dfa04b4369cfc60342f7d6e

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 506b1a27c322908a696ff21b
ciphertext: f713224d98ab0f41e19dee499a69b002dc0eeb4ed2f1d25bc51c8d46872e
6658b8b727d85d7fe3c5f2496dfc2d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 506b1a27c322908a696ff21d
ciphertext: 87a207c668e277338124f24283fd2fead99ca9e7758e2a261a0b1e23c804
aeccaa8c9db788fec59a4ff60d9d01

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 506b1a27c322908a696ff2e6
ciphertext: 2f206ae4f0c305ca7bb143e5799d3fc1ca3f1967907ee2cefe354b607582
e6da5ee2c151ed4e006ac0bea0b705

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 506b1a27c322908a696ff319
ciphertext: 45663902baba32b1d4bc30bdf6bc84fd0d6c75d8183171798d660683e20b
0da5eed47cd4a1d8e50e724d3d92ff
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
bee5710e3cdbb45ccf19225c70e441d59f9f5a03c8d18265b535184479ef99a8

exporter_context: 00
L: 32
exported_value:
0946a53f89b63824aede60e9a39349dc60e645401ef6a8b20a4b96912e13a944

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
d4b25aa19d6c39e24a6a33b449e0a601308fb4273c74a07831dae99ee31dd5fb
~~~

## DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, Export-Only AEAD

### Base Setup Information
~~~
mode: 0
kem_id: 32
kdf_id: 1
aead_id: 65535
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: fd25fee6390a3e6ac22a2803bb7ad8a5cb5840909cd9eec5477861fcf80e95c6
pkEm: 3dd7692d425314fbdafe93d30b270b6a6b1334a3fd91ffcdf7dd5f2e47287e19
skEm: 0c936a530f1fefef3dc36824d68dec25c8a45cdd65b2c2d509d4e729de864199
ikmR: 0e92d2106717b970b151fcd12b3254acdc7a5d1b404970447b36dba57322e2a3
pkRm: 7a71e8fb1172ce7911aae98fc95f3dfabee0ca941ad4f7a80cd1e12cc3ac1a0f
skRm: de14dc512e274f434203e210891a2126e080d877f634b81ed99819055fdd9a75
enc: 3dd7692d425314fbdafe93d30b270b6a6b1334a3fd91ffcdf7dd5f2e47287e19
shared_secret:
69e652a203f63aaaeeda4251629db85e3a86c400b7e6c0af66e6b7c65829a460
key_schedule_context: 003d46e6b74658a4c6178186c0256fcfbb80388dfced042733
31809098351cc19d56a7644fe2c4ed575dbd11f82d995403da7875c62d59381862798f75
71b0e9aa
secret: b2841af7aa53b01e042bfb39b1dc45135050badfc3fa5d281f4f105659d22d6a
key:
base_nonce:
exporter_secret:
26984b32209a528926a617fb1bacd8e394bb137ec136556ff8d93019e36fdc2f
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
3ce6bd2dd444ec89a6fc1f530b05bf4147a01ee783e0696479832c680aa93fa1

exporter_context: 00
L: 32
exported_value:
f3c6d57e1f355ab143ee1bca88c059dc8b6bdc933d8489d01afa637a012118a3

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
5a9527dfb98087e0e0c57ec3cd8064979242f3f316ac66e0877f01d9b91d1f92
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 65535
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 0b1e8a08ab372010dcbffb81a133ccab19393b3566bd348d7ee14e3756a0742c
pkEm: 689e540564c01729f650eaa1268d166581faa17880fef0d4f71aba4b99c84879
skEm: f523df71b0e5dc36d6357124e9df29fb0210203dc68cfd1a095134a3c448f6fd
ikmR: fe22b2df8c8a5c83a61309ae5c8cacbcef66a0a5ab272f365fa7e9ca313ba988
pkRm: c407e88d9aa29930a3b0a80d5bf6c6a61ca9ffd82ea1a19aad2d81a19a44ee1c
skRm: b5cb06a707b4ff5fb002322eb61df776f4c21e234e317d1130b6e55b690ef3f3
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 689e540564c01729f650eaa1268d166581faa17880fef0d4f71aba4b99c84879
shared_secret:
95cf26b7bb1c3482528cdf535701917255f2a92932e7716d17857cbe4728b843
key_schedule_context: 01771a4a301d8c0172c15f39ef4c403817bbef77efb9f826bb
4b2ba5cd43b6169456a7644fe2c4ed575dbd11f82d995403da7875c62d59381862798f75
71b0e9aa
secret: cde26ee46a8e18ae767f856cd79cdef1c64ff4229710c0205e7e8c44e8e0fac4
key:
base_nonce:
exporter_secret:
426c1002a7bb83968ad38191561c1286ef50d84f6b12f1cdfceae437f5ae3585
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
0afde49f42e7d63376f85586534983c94e06af873a7c28c79a5422b71e176478

exporter_context: 00
L: 32
exported_value:
8f413a30d2839a2e64a7aedbff817d07475a1f9321d385f74f11b1373a49847f

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
19134871abbef7cc8a5aa6eccd04733cc266f607dfba7cdc2d7e86aaf421f97c
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 65535
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 354f6caefa215f87e9c783edacbc33f1892153a2fb9b358e766e30ff3283ae42
pkEm: 7fe0da26c3d0b589990261d7a04c90fc73c5240d11f73eabb459a5bf875be608
skEm: 3a2af8a9e4309b3b777d58437f13ed2cadc820b3b7465c9e227ab2f57998239f
ikmR: 50e916b01df1eb4ca7fad822b7f448579d9ed6046dabf917ebc6460da9082b73
pkRm: a9b03c18e25100d4dece73844cb1db2e5787567f84a948af411dcc7f43ebe962
skRm: 94a80804342a0df234bf6bdbd3b16c23b7b0803f0c1133e572da9a63bcf96233
ikmS: 0c9b2083832ade0e86e635639b6e2b60a1a51d6ad495f49da221f290e89d08cb
pkSm: 7feea4f2d7e48765042e053bd89c39c5a50ee9c20a6bae4086a9f17cb6119e01
skSm: 658a21e96d5d2fb6d1c1d4f31dea225652457d53d245201c858637eb60876f9f
enc: 7fe0da26c3d0b589990261d7a04c90fc73c5240d11f73eabb459a5bf875be608
shared_secret:
57d627f15d2876222f2558a8080c806a193a10605126be7f2467025dad635fe2
key_schedule_context: 023d46e6b74658a4c6178186c0256fcfbb80388dfced042733
31809098351cc19d56a7644fe2c4ed575dbd11f82d995403da7875c62d59381862798f75
71b0e9aa
secret: 2d58089c497d3908d6b11fbc5619fd9c1297ad0f9e435174d805bd1138767639
key:
base_nonce:
exporter_secret:
c123f918736c12f532a57b073d4bdc14a60111ae19f14bd2e8215cc2c07eb787
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
22379fcb605adc88d3845914b863710b93627208e91e272553136e8a8352f8c0

exporter_context: 00
L: 32
exported_value:
34899d55939a49c4080102e0a0ddeb25adaae11ffcb86421c1d2ca0d97835ddc

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
302b4e7e121f6b0688f64f0b4ac18ea7f0b34bdf3b80b4e2d18c15d677f10069
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 65535
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 9b11f0f5d478e01039dea03ff9dd3be09bf658bbae353eba10daae44de5b3db7
pkEm: 2990ffd43ebdc605493ce691731dfef3bfe8cc95ddc51fb1e60c494c30b88f18
skEm: a9d2cd9459f2a799701d995e49adef541c73137e93ae6889cfe28ba1e54f0052
ikmR: 27aac8140906b3821c7a423b362b6a30ab964b246e9ba8c7fccc5201c30ccb83
pkRm: 7822195255235325b19d65f2cab89801d59b9677b8697bba9ee7a27849c5a353
skRm: 3feadefdc39e82a355a52d912cf2467df9c6650580484cb6eef23af89b1a386b
ikmS: 0a935724b0cf5f51910079665a4175aa83aa4882a1ebbd93b54fa2cb00155723
pkSm: ac058bf5eb28717a8f12c8c5bbcbc42328ae8d5951ec0570796b43d4caf60962
skSm: 94834fed3c583bb8dd79f4574e1a69ab616963b19ddfb375b8a58510b906cdb5
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 2990ffd43ebdc605493ce691731dfef3bfe8cc95ddc51fb1e60c494c30b88f18
shared_secret:
d3f1e60e497270d40c5f4f96a964a0983164a07be6357627c99790720b432f34
key_schedule_context: 03771a4a301d8c0172c15f39ef4c403817bbef77efb9f826bb
4b2ba5cd43b6169456a7644fe2c4ed575dbd11f82d995403da7875c62d59381862798f75
71b0e9aa
secret: bc6d1f12ce23bb6fa9d2d17b800fe69024964cee4577dc2162c0c050f1f23242
key:
base_nonce:
exporter_secret:
5b85ceaba3f301c7cf01c1f0aeba71678f11a74618a6f09c6ddbf65f6ef432c2
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
573c24d581994a81a6518ee5b1d48abf85b1cc38fc8f70f01de1cdc7f5bf2ee8

exporter_context: 00
L: 32
exported_value:
6fe60913b0a0af95ac071d7b53d83692970b5b4c030bc8a2e0074671eb4002c1

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
d2b79beaacda50f1fca777e8f2d0f7b70dd296b6a2c18326816d6e11a6d5860c
~~~
