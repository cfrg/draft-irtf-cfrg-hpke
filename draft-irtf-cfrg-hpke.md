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
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/9dc6a7611390b1c4e8068a73e50c4988a80f078a/test-vectors.json
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

- `(skX, pkX)`: A KEM key pair used in role X; `skX` is the private
  key and `pkX` is the public key.
- `pk(skX)`: The KEM public key corresponding to the KEM private key `skX`.
- Sender (S): Role of entity which sends an encrypted message.
- Recipient (R): Role of entity which receives an encrypted message.
- Ephemeral (E): Role of a fresh random value meant for one-time use.
- `I2OSP(n)` and `OS2IP(x)`: Convert a byte string to and from a non-negative
  integer as described in {{!RFC8017}}. Note that these functions operate on
  byte strings in big-endian byte order.
- `concat(x0, ..., xN)`: Concatenation of byte strings.
  `concat(0x01, 0x0203, 0x040506) = 0x010203040506`.
- `random(n)`: A pseudorandom byte string of length `n` bytes
- `xor(a,b)`: XOR of byte strings; `xor(0xF0F0, 0x1234) = 0xE2C4`.
  It is an error to call this function with two arguments of unequal
  length.

# Cryptographic Dependencies

HPKE variants rely on the following primitives:

* A Key Encapsulation Mechanism (KEM):
  - `GenerateKeyPair()`: Randomized algorithm to generate a key pair `(skX, pkX)`
  - `DeriveKeyPair(ikm)`: Deterministic algorithm to derive a key pair
    `(skX, pkX)` from the byte string `ikm`, where `ikm` SHOULD have at
    least `Nsk` bytes of entropy (see {{derive-key-pair}} for discussion)
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
  - `Nsecret`: The length in bytes of a KEM shared secret produced by this KEM
  - `Nenc`: The length in bytes of an encapsulated key produced by this KEM
  - `Npk`: The length in bytes of an encoded public key for this KEM
  - `Nsk`: The length in bytes of an encoded private key for this KEM

* A Key Derivation Function (KDF):
  - `Extract(salt, ikm)`: Extract a pseudorandom key of fixed length `Nh` bytes
    from input keying material `ikm` and an optional byte string
    `salt`
  - `Expand(prk, info, L)`: Expand a pseudorandom key `prk` using
    optional string `info` into `L` bytes of output keying material
  - `Nh`: The output size of the `Extract()` function in bytes

* An AEAD encryption algorithm {{!RFC5116}}:
  - `Seal(key, nonce, aad, pt)`: Encrypt and authenticate plaintext
    `pt` with associated data `aad` using symmetric key `key` and nonce
    `nonce`, yielding ciphertext and tag `ct`. This function
     can raise a `NonceOverflowError` upon failure.
  - `Open(key, nonce, aad, ct)`: Decrypt ciphertext and tag `ct` using
    associated data `aad` with symmetric key `key` and nonce `nonce`,
    returning plaintext message `pt`. This function can raise an
    `OpenError` or `NonceOverflowError` upon failure.
  - `Nk`: The length in bytes of a key for this algorithm
  - `Nn`: The length in bytes of a nonce for this algorithm

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
  labeled_ikm = concat("HPKE-06", suite_id, label, ikm)
  return Extract(salt, labeled_ikm)

def LabeledExpand(prk, label, info, L):
  labeled_info = concat(I2OSP(L, 2), "HPKE-06", suite_id,
                        label, info)
  return Expand(prk, labeled_info, L)
~~~

\[\[RFC editor: please change "HPKE-06" to "RFCXXXX", where XXXX is the final number, before publication.]]

The value of `suite_id` depends on where the KDF is used; it is assumed
implicit from the implementation and not passed as a parameter. If used
inside a KEM algorithm, `suite_id` MUST start with "KEM" and identify
this KEM algorithm; if used in the remainder of HPKE, it MUST start with
"HPKE" and identify the entire ciphersuite in use. See sections {{dhkem}}
and {{encryption-context}} for details.

## DH-Based KEM {#dhkem}

Suppose we are given a KDF, and a Diffie-Hellman group providing the
following operations:

- `GenerateKeyPair()`: Randomized algorithm to generate a key pair `(skX, pkX)`
  for the DH group in use
- `DeriveKeyPair(ikm)`: Deterministic algorithm to derive a key pair
  `(skX, pkX)` from the byte string `ikm`, where `ikm` SHOULD have at
  least `Nsk` bytes of entropy (see {{derive-key-pair}} for discussion)
- `DH(skX, pkY)`: Perform a non-interactive DH exchange using the
  private key `skX` and public key `pkY` to produce a Diffie-Hellman
  shared secret of length `Ndh`. This function can raise a
  `ValidationError` as described in {{validation}}.
- `Serialize(pk)`: Produce a byte string of length `Npk`
  encoding the public key `pk`
- `Deserialize(enc)`: Parse a byte string of length `Npk` to recover a
  public key. This function can raise a `DeserializeError` error upon
  `enc` deserialization failure.
- `Ndh`: The length in bytes of a Diffie-Hellman shared secret produced
  by `DH()`
- `Nsk`: The length in bytes of a Diffie-Hellman private key

Since an encapsulated key is a Diffie-Hellman public key in this KEM
algorithm, we use `Serialize()` to encode them, and `Npk` equals `Nenc`.
The same applies to `Deserialize()`.

Then we can construct a KEM called `DHKEM(Group, KDF)` in the
following way, where `Group` denotes the Diffie-Hellman group and
`KDF` the KDF. The function parameters `pkR` and `pkS` are deserialized
public keys, and `enc` is a serialized public key.
{{derive-key-pair}} contains the `DeriveKeyPair` function specification
for DHKEMs defined in this document.

~~~
def ExtractAndExpand(dh, kem_context):
  eae_prk = LabeledExtract("", "eae_prk", dh)
  shared_secret = LabeledExpand(eae_prk, "shared_secret",
                                kem_context, Nsecret)
  return shared_secret

def Encap(pkR):
  skE, pkE = GenerateKeyPair()
  dh = DH(skE, pkR)
  enc = Serialize(pkE)

  pkRm = Serialize(pkR)
  kem_context = concat(enc, pkRm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret, enc

def Decap(enc, skR):
  pkE = Deserialize(enc)
  dh = DH(skR, pkE)

  pkRm = Serialize(pk(skR))
  kem_context = concat(enc, pkRm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret

def AuthEncap(pkR, skS):
  skE, pkE = GenerateKeyPair()
  dh = concat(DH(skE, pkR), DH(skS, pkR))
  enc = Serialize(pkE)

  pkRm = Serialize(pkR)
  pkSm = Serialize(pk(skS))
  kem_context = concat(enc, pkRm, pkSm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret, enc

def AuthDecap(enc, skR, pkS):
  pkE = Deserialize(enc)
  dh = concat(DH(skR, pkE), DH(skR, pkS))

  pkRm = Serialize(pk(skR))
  pkSm = Serialize(pkS)
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

All these cases follow the same basic two-step pattern:

1. Set up an encryption context that is shared between the sender
   and the recipient
2. Use that context to encrypt or decrypt content

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

* `mode` - A one-byte value indicating the HPKE mode, defined in {{hpke}}.
* `shared_secret` - A KEM shared secret generated for this transaction
* `info` - Application-supplied information (optional; default value
  "")
* `psk` - A pre-shared key (PSK) held by both the sender
  and the recipient (optional; default value "")
* `psk_id` - An identifier for the PSK (optional; default value "")

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
AEAD `aead_id` 2-byte code points as defined in {{ciphersuites}}, are
assumed implicit from the implementation and not passed as parameters.
The implicit `suite_id` value used within `LabeledExtract` and
`LabeledExpand` is defined based on them as follows:

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

The `Auth` column indicates if the KEM algorithm provides the `AuthEncap()`/`AuthDecap()`
interface. The meaning of all other columns is explained in {{kem-template}}.

### SerializePublicKey and DeserializePublicKey

For P-256, P-384 and P-521, the `Serialize()` function of the
KEM performs the uncompressed Elliptic-Curve-Point-to-Octet-String
conversion according to {{SECG}}. `Deserialize()` performs the
uncompressed Octet-String-to-Elliptic-Curve-Point conversion.

For X25519 and X448, the `Serialize()` and `Deserialize()` functions
are the identity function, since these curves already use fixed-length byte
strings for public keys.

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

This shows that the limits are only marginally smaller than the maximum
input length of the underlying hash function; these limits are large and
unlikely to be reached in practical applications. Future specifications
which define new KDFs MUST specify bounds for these variable-length
parameters.

The values for `psk`, `psk_id`, and `info` which are inputs to
`LabeledExtract()` were computed with the following expression:

~~~
max_size_hash_input - Nb - size_label_rfcXXXX -
    size_suite_id - size_input_label
~~~

The value for `exporter_context` which is an input to `LabeledExpand()`
was computed with the following expression:

~~~
max_size_hash_input - Nb - Nh - size_label_rfcXXXX -
    size_suite_id - size_input_label - 2 - 1
~~~

In these equations, `max_size_hash_input` is the maximum input length
of the underlying hash function in bytes, `Nb` is the block size of the
underlying hash function in bytes, `size_label_rfcXXXX` is the size
of "HPKE-06" in bytes and equals 7, `size_suite_id` is the size of the
`suite_id` and equals 10, and `size_input_label` is the size
of the label used as parameter to `LabeledExtract()` or `LabeledExpand()`.

\[\[RFC editor: please change "HPKE-06" to "RFCXXXX", where XXXX is the final number, before publication.]]

## Authenticated Encryption with Associated Data (AEAD) Functions {#aead-ids}

| Value  | AEAD             | Nk  | Nn  | Reference    |
|:-------|:-----------------|:----|:----|:-------------|
| 0x0000 | (reserved)       | N/A | N/A | N/A          |
| 0x0001 | AES-128-GCM      | 16  | 12  | {{GCM}}      |
| 0x0002 | AES-256-GCM      | 32  | 12  | {{GCM}}      |
| 0x0003 | ChaCha20Poly1305 | 32  | 12  | {{?RFC8439}} |
| 0xFFFF | Export-only      | N/A | N/A | [[RFCXXXX]] |

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
an identifier different from "HPKE-06". Particular attention needs to
be paid if the KEM directly invokes functions that are used internally
in HPKE's `Extract()` or `Expand()`, such as `Hash()` and `HMAC()` in the case of HKDF.
It MUST be ensured that inputs to these invocations cannot collide with
inputs to the internal invocations of these functions inside Extract or
Expand. In HPKE's `KeySchedule()` this is avoided by using `Extract()` instead of
`Hash()` on the arbitrary-length inputs `info` and `psk_id`.

The string literal "HPKE-06" used in `LabeledExtract()` and `LabeledExpand()`
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
ikmE: 11bba1578b0abf571cf6b835f804c9cf361fe9f835f39ec3f620068be391f391
pkEm: 4dd4292ba513fcd6821c37e38fd0d14d91f0281717c4d5602e8775d95f755734
skEm: 26a5af77c38f13a9e8cecc25473bca2d592db09f94c3c98c828a5be227ea7634
ikmR: 4d16eec05f8766a69cd2137c165fe7b2dae6334064b5047c7b6b3785fd9915f2
pkRm: 681a56e0158676377b51ef1ae5f0f8906f5509f32a6c15609ef51bc07e849462
skRm: f5dda03033ef96cc32c53636bd8b0c1a241b0a4392e467afa241a088977633f7
enc: 4dd4292ba513fcd6821c37e38fd0d14d91f0281717c4d5602e8775d95f755734
shared_secret:
0ca2e250781fde3c871251f23b5cbd59a8fb42afbc9f531f095315e6314d5693
key_schedule_context: 002acc146c3ed28a930a50da2b269cb150a8a78a54081f81db
457ac52d5bd2f581cb95a2c63b1dac72dc030fbe46d152ccb09f43fdf6e74d13660a4bd8
0ff49b55
secret: bab0cf2d0f68815a59f5d4973598eb97c414c1c1638094f8d3af7b5f6e371f1d
key: 69e7eb3519e123648cdcd545ef6c72df
base_nonce: 24d5f53f5aca5b3061155841
exporter_secret:
2f7533456f55c4f3d57d10c0cf7755d7012977c7c0be6f5a7ab386cef1fd2b0f
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 24d5f53f5aca5b3061155841
ciphertext: f85f446133f8d801c88325df4143b187d399a557c7d56c5771f253dc7deb
f776b8910d7f9b0306e177b97d7183

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 24d5f53f5aca5b3061155840
ciphertext: f90367fffa26b2ea5ff96a7e147b12ecfe7e287890a1d1703b9578a34c15
9cd53c71d0374bcc56bbfbfe1d88ca

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 24d5f53f5aca5b3061155843
ciphertext: 1d68e823525a7f2265aadc60bf146b6158f0b21b7ca8c62850ea91d05d0f
1404368022ad1def071a92e8bdcd62

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 24d5f53f5aca5b3061155845
ciphertext: 3a9196f3616bddd03b73f4cf1cbc57a12c0a8f45663e9e4efdce2bde25c8
7594c1b5cba33c2e093f7f9e419471
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
f062f752927f06bd410159152d0514bb19b9dd4868f1c376d73089d837e23db0

exporter_context: 00
L: 32
exported_value:
0106d1b888c7ac14dc9b693a3db6122fb20e23ff8683623d90ceb9e73f39a4b9

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
8b6dea1ddd2184442e196ac714776922e2a37ba1b20f9b4fa631fe42f5f15bd1
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 42b7140de27ac953b49f4cb394b5a30f070d42f43ac9a6d9226028d092e9f0d9
pkEm: d9d9d4956ea135c3ed42eedf9a1b7ff9fd74ba98c982bb369351bb2fb74af473
skEm: e645e664e34bfa8d4f1daad61fe8376e915cdd4656595350a83d765ebe7f0cbe
ikmR: e01b1e56b840e2c48fe1d63f546a8d3f7a92f5def29c8284dc19cb199e9ff1f2
pkRm: 431249ba4cd0f108484b63c4a32a278566c90a0866db983677eed0429a8cfc4f
skRm: 74662cc5971661e81a98cfd446fcf725627229fe862925fe263f6ccc8cde2d6f
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: d9d9d4956ea135c3ed42eedf9a1b7ff9fd74ba98c982bb369351bb2fb74af473
shared_secret:
b352972c2db19336720103904d7afad32a80e84fc7ad644d8029f176a3e837ed
key_schedule_context: 01deb296ccdb4fa0a001eef56dd3b10577b30352610d1639fd
5738efd4acb8e4e6cb95a2c63b1dac72dc030fbe46d152ccb09f43fdf6e74d13660a4bd8
0ff49b55
secret: cda3487006caf2e745846f2556eb9fcba2c14daef3b1d7aca20052604b62f288
key: 534fb9190e66b8d2932ac6bcf66f656e
base_nonce: e00ff9609876947a26f2025b
exporter_secret:
7c4222c2c2f82ecd897625ffecb76b13be7056ae250dbb01378523fdf2d4657c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: e00ff9609876947a26f2025b
ciphertext: dc92438f4372a973525eb990b3d5720c46a76df1b6b4e7857aee49af1c7b
294538aada5e93db52a2a3fce74922

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: e00ff9609876947a26f2025a
ciphertext: e5b7f1ba96fa550dce89e97245264c04daabccbc7edab8010d3b66bb25c3
96ea6a348b5909a14e087502b8eb09

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: e00ff9609876947a26f20259
ciphertext: bdbc00d77740a165de8e0ffe049932c09df02ad04183907dd7ebda16df25
e38a03b0ed69e47509775263f335b3

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: e00ff9609876947a26f2025f
ciphertext: 03c33fe776539abf3bd2adf1ef95990f6617395b27a94b7c4b5456ab2050
6bcb86227ab4512b82c4049e14ae99
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
464f9f270b1e9c3b7511080c007241b151ee3b2aca87d1df6ef702b04b85ca83

exporter_context: 00
L: 32
exported_value:
1c7fd659d4120b695cc3293d5d13c2e8ba0b5166c267e800aaf1c43b091c8246

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
7636a65f4618bdb1a236ef38702ef4c1fd89699210b9afd2898dd750fc33503e
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 355d7a513050811d6cc80144e7582b03549c038531a9c852d1891cb99873d0ba
pkEm: 02cd4cda1029a62181dd9efc92bfbf24017a1d8646d8056d3d8ca6c79205662b
skEm: 992453560b52c7aba7b4c005f709f88f4a354dd19a4a8c9cb8ff5a83a247daf5
ikmR: b7401b6cb896f789e2369259ff05c28a288bd38ced7c66c7f655fa5fd100a9d4
pkRm: f93c4552c4a38ef118c4834192bdee81dfe4d6310f686a1b84c545fcc6755d22
skRm: e43c85c9c5ea81d8d734a81eaf4992fd3ea4c354b09295821e1855c84ff99872
ikmS: 12cf20d4bec43f122b04b116778982ecd65e8e5a11f03a3087a177d0f487de99
pkSm: 3d64671c06619c45fd5d60390660f941c47c909ad3bbb603545fc99152dcd215
skSm: 5de4ee1d33aa9ae8d6c7b6ee3b820b6611bcb3c142b689dd578c5440e6eb72f9
enc: 02cd4cda1029a62181dd9efc92bfbf24017a1d8646d8056d3d8ca6c79205662b
shared_secret:
8cc8023ea761158922bc6599ebb75f0d7370dabfac4ddb1bda3c3f8e3525c43e
key_schedule_context: 022acc146c3ed28a930a50da2b269cb150a8a78a54081f81db
457ac52d5bd2f581cb95a2c63b1dac72dc030fbe46d152ccb09f43fdf6e74d13660a4bd8
0ff49b55
secret: 8c8b1d41e70f3b014c132fa6d7e4142935d70f68db74edb4a3360940da5c11a7
key: abed1ee4d57fa5eba68c4a2e0878a7d6
base_nonce: 10295d084092db1cb8f5c0f6
exporter_secret:
a7fc50b1e113b56c3084edb91166a7ff7c7dbb7edb3e0b2f12bb5830a8120105
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 10295d084092db1cb8f5c0f6
ciphertext: b802f41dc861caed86904065e2d23a38ed78ae6860fdf866d4068cd20aad
181f0318e7e5587c4effe7b6789d1b

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 10295d084092db1cb8f5c0f7
ciphertext: 279723960f9c2f22d9e4fae6a08efb4a1c8d24f9312425ad9d45e2121c20
15a379c0aa4e00139d78826417ba2d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 10295d084092db1cb8f5c0f4
ciphertext: 86270a3ffe82ac06c9a6ec47a6e5d12e50efcc5b4c2875ea65e918a96a70
06df0b6a38beee24fcbcb5a7e96351

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 10295d084092db1cb8f5c0f2
ciphertext: 3425843d995b448d8f7e91c159be7e8f8f465335bb1caa1d69f737686081
a97b48890b3338932a8ec2bdf84c23
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
d386089a3e2625915c2c4c73926954bcd864d746238c0a6c6cfb119dfccc58bd

exporter_context: 00
L: 32
exported_value:
f157400fca9a59d2783b8ad2892c268b9b513e04c34877167347b8da9bd7e04e

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
8d05d6cab15cd663ee469cf6999b32fe39999e038e02324ef183f0db66c9d6f9
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 4d1b72dc3648906b631cd427c65df44106c6c39d9df4b55eb4a0291de044acc7
pkEm: 02502a5b123bf2712ed2287e5685c78e20c0057b28f76d0c5661727d222b5a73
skEm: c64f9e6dd3b9648b9aee6d0ee887b515be3c8e27ffc34bff41f62335c12eb5e7
ikmR: 0aac672e885d50ae96b7b712e220d6535fcbecb7fdeeaec75209eac344b6179c
pkRm: d6a6368e2a473f820fa2790ed7cdfac60dcd04ed350abe64f7ee674d32bb5821
skRm: 9480fa77d6023f98fa45e983752533f40945f2c659f62b8f21f01b02b9fb61a3
ikmS: c09351c079f4f62d427a66a858a3f52b9ccae63498c0253738da1865d22e68dc
pkSm: 46e26b7808ff0dd3eb8c3f6e48475808514275ff2d09bcb98c06e5b2597ee83d
skSm: 72201967a577b61928b0c4d6285005d8dc09a372f9233b93cb29c399fbfc9f65
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 02502a5b123bf2712ed2287e5685c78e20c0057b28f76d0c5661727d222b5a73
shared_secret:
572277e9790161673804b61c258749eb9a568e9ea7c6476c267c21bf0f760cb9
key_schedule_context: 03deb296ccdb4fa0a001eef56dd3b10577b30352610d1639fd
5738efd4acb8e4e6cb95a2c63b1dac72dc030fbe46d152ccb09f43fdf6e74d13660a4bd8
0ff49b55
secret: 41391a81b54fa74287793b1b448a96b7c775bc4bc8abcbd7d6e744659bc6e83f
key: 906ba56b5c1513f67f08ec0c3c7d07f2
base_nonce: 399ee1d7e7e8ea7ad8af1fb9
exporter_secret:
e8e5c11294604171c86e9536ead1af3a7b9f193c28704966c63083982440731f
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 399ee1d7e7e8ea7ad8af1fb9
ciphertext: c1728a09c78780a3ca25d213dff8505cc463b7e23a6c8777623db38fb239
48ca4f9a12533577465294895065ed

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 399ee1d7e7e8ea7ad8af1fb8
ciphertext: 3e1be8be5ed9a2dbbc3f7d4ac57dae304a94238f992fd2f1c7a2d2679aa7
ee4b4c8d81bf779855b8906420e3a7

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 399ee1d7e7e8ea7ad8af1fbb
ciphertext: 5c5e581ce04e061f71b1118a67d129c956bcc18031f9981086748da060e7
a5298f3ece8f71f04cf481d4ff713b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 399ee1d7e7e8ea7ad8af1fbd
ciphertext: 832b904bca3a869ef87192ac82416ee9f447a86433f2a72da42d1da71f91
a95ac35fd8204e97f539787eaf3858
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
0e943d0d61dbb67a5b63c71df5a560e97fb3cdb050fa473f814dd7e664ff743a

exporter_context: 00
L: 32
exported_value:
75e88468800e37ebe16ba5424820a3aa569c5304e9912bef3969d03648517879

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
a329de91439938fb1b9a46faa64aa99f8dc648c5a398e9c90c40232efb1bb699
~~~

## DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 15172baf7d1cf19a0e7b12fc8baa2c832398658d0fe53bf0436fc4e16868db25
pkEm: d3b4ae1e73eb0a189a7c98996fc514b4aa0bf6be1290c36df033ac3a534a083e
skEm: 93fb891896eeb4cf19717a17dc43240584804fc42cd4d27d249da7c0064801b1
ikmR: 7864187fa06de381987800466fc548f13f713fc9d69b29128ae0ccaf48139e17
pkRm: f1e824faa95410fa7bde32713d41bcd2c0f47b42b1ad94602e6d70ef59c3cc01
skRm: 0cde1fe3ffa01cedf65b716f110700bfbd1ae5ae7dc8d14caec3c7d8d1d30dea
enc: d3b4ae1e73eb0a189a7c98996fc514b4aa0bf6be1290c36df033ac3a534a083e
shared_secret:
1c7151856c466656fc7a1bf49301430fba682e943ed52d73e4bf3b88fccb75fc
key_schedule_context: 00dd0a37ad96727124b021d7c81c42bfbb68c11f38050b13aa
54adb5a92dd165760f0d33c7dafc645fdc165ad9d110e77f68358179ad974a9a9b71dd05
5dec5eee
secret: 1aed2cab9c368bd510bfb63ba2fbaba028a8da33dc870642df8b25bcce81ec6d
key: 15954e13402a20e56dc3331835acf51fd53da32cdd67147440627f8eb40eed5e
base_nonce: f608d830fa7d7e3c1d06aa3c
exporter_secret:
b670f69997f79cf2c8712e14d9bdc36265c63fef8d1645d4d2ec68b322362b42
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: f608d830fa7d7e3c1d06aa3c
ciphertext: 306e13b26fe3439364cbb1807e10c87473c7a1c7bdee4519d52f2006f82d
b21cca710988ad760daa90c0dfe677

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: f608d830fa7d7e3c1d06aa3d
ciphertext: 4629081348772f541479b1c5afd675b5780be6111b66f4d1340c6ce0e506
2d7c025c81f329da9d33efb60e2dde

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: f608d830fa7d7e3c1d06aa3e
ciphertext: 59f3c9354442bbcc271dd4896cb8c9da1099d4d50e84f5cf4ac5673f3141
c41325963492a6d3c8b6543b09fc2f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: f608d830fa7d7e3c1d06aa38
ciphertext: b27d4fb5c1ab7b29214a2c69d306548e61686d9c19b14b88fd61e98a17ca
63937a35288b03dc8baf0d7f4a3fb3
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
70d85c9888ab19fd44e910e6edef4a753fad67b2da46f3bcdea070a8890c348d

exporter_context: 00
L: 32
exported_value:
9789370ac9353318a2900e90aa084d348a19f6fb33833401c4306b7e95a409ef

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
5e03541cae05ffcc54004e4d71c56702d4bcbf1db5937f0aa3b5180357e285ac
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 389026048d994d39c5b267a368463da7c9585877ac368c7b7054473e9877ba28
pkEm: d79ea436c8f3d36f57522911c2709dd9dd95a56de71b5cadd1ce5c752c8c913e
skEm: a8480ec7cf10ff09ed266801dee0a58416e7f4aabd8f4705a67c52e8777f1014
ikmR: 11a920efdb576dab964ff7763fef4aef94889474a2e3e6f9f9ce7e84d6a68041
pkRm: 5cc3d917df7a42ed5a8a3cf1805d622330a97eff954557a5af5cd6c8e6c2ee5e
skRm: 8c431f0bb23c96d91217d9e8868d5d28b61f87db1cd6315f65170ab9235f3b34
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: d79ea436c8f3d36f57522911c2709dd9dd95a56de71b5cadd1ce5c752c8c913e
shared_secret:
5a3e7b8dc51779fde7e9421684fa29d3c6b97b043aeea2db9c08ca0183dca67f
key_schedule_context: 0151af0d3a80f50ff5d606ae45bf724c2f872698eacd389476
90bf75e1262a72a30f0d33c7dafc645fdc165ad9d110e77f68358179ad974a9a9b71dd05
5dec5eee
secret: aae45cd22a624913f56088d818f9ad23f8ab17a1b1f58a9209e48da9b5723a0b
key: 9c3fe404069e4e8c605b80bc172b9be7ba5bdee0576856561136050098f33c2f
base_nonce: a31692d2ce105cdbece2612e
exporter_secret:
726bedc247af0bb8f3854d54b896950a3118315586d41055f01e59e2cd83bd38
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: a31692d2ce105cdbece2612e
ciphertext: e7c59bbcc74f448970eefd2acd7d7119bde0cc50f5fcfb135cb13c0c8997
9aab1d5d23eb1fe0667bb3106e063f

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: a31692d2ce105cdbece2612f
ciphertext: 1906a4fe3778dc84d445e44e1b08057ad37a4af449516ec89fd72984278f
48f3291a0f40e413eba46258318607

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: a31692d2ce105cdbece2612c
ciphertext: f185ff3009a248c5759947c75431369f403ea4af11f0f63c9a40591b5a11
9c6660071c73529311851d9181ace7

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: a31692d2ce105cdbece2612a
ciphertext: f48cf5a4aaa9652c55a0b6a2d1965005f4e680d4e93d4c1eda7ab84d54fb
d88636d10c92256cd0eeabb6d6a0cd
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
c6eabe8efbe676592a1c65884dba977c076764654e5d7b2584b96d0593fc1506

exporter_context: 00
L: 32
exported_value:
f3af1197203f6079b72c4394d3d1bf032cb918246cb5e3e82a467c0c7f702411

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
721888914fcb92d4087e28f8d44500b6b86ef6f7bd857eb1f164fd996826dcd2
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: c7d0c63b4ed9d0e27094fbc6d599a2e04326d7d85327daa2e90bda9858721e92
pkEm: c817b168a0f0bcd23a3773a41900903a02edaaa81bb65f2d3421591b94370703
skEm: f1df9ff4cd1d2750bbb5b926b05472156a65cb15bde5120566f90c281f43b5f8
ikmR: 9f118b4e04338df3eb6af25f9349c05cd2a00c597d5e8103c32d7dca427eb09a
pkRm: 3d8842f82174d003815a14b5c8aedf79ba881acadb48f95dd89007c222213e49
skRm: aad95974d78406642ec048461203804acb311f1fa07cf27f4927320ef2721f90
ikmS: ba7d8cbd2f6cd60760799be10c2248a07e4b309e2f651d3fe3869e69c264a3db
pkSm: 39ae186a4d9e5f734b7cdb78a43db8770f2f8f7a1cc9c1b4616b108129c14d35
skSm: 1dd6d2e9e82bea9285ca8cf7ea04b9d1a8529d8920397f7c6848eac2ebbf1163
enc: c817b168a0f0bcd23a3773a41900903a02edaaa81bb65f2d3421591b94370703
shared_secret:
548c7b973000ca12d471633401587c510d215082debccf8605bb8ebc376f13c5
key_schedule_context: 02dd0a37ad96727124b021d7c81c42bfbb68c11f38050b13aa
54adb5a92dd165760f0d33c7dafc645fdc165ad9d110e77f68358179ad974a9a9b71dd05
5dec5eee
secret: 5533cc99cf68aed46512732049b31cab61520c972a37f35e8dd385ce9048ef26
key: 2c7f10cb2bc164263d53064e95f2c45aafbfcb323f1d2331ec22d6632e1b86d1
base_nonce: 1a177374722543cba5196def
exporter_secret:
e251118dc1d73b36f5b029558aa7a6b75585257b731949baf7482bf8b4a7d457
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 1a177374722543cba5196def
ciphertext: b4dc14b7325e53a7715fef7daf571c99cf0a6956158876b883166308e979
2c659c07b3525afff2eb302cd77805

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 1a177374722543cba5196dee
ciphertext: 6b02a525eebbafd935da44826f44f2a06ef955c373be610dad307d1dfcf2
bc366f6613c5c16c269459107c8ca1

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 1a177374722543cba5196ded
ciphertext: d5f69d1d3163a18043278ae8844dd16eab2a93e79be29d3274afd6fe6b01
d1f5433e60b18c7c7a59d1119559e3

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 1a177374722543cba5196deb
ciphertext: 5047f34f873864c0006b50a73e100f4000ea78d40f84b7ac1f3fab1b70c2
55e9e66132b4a287cc5e78eecbb4e6
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
d007126899388e8d8d976c359a9f04db9ccce56f8300c8b57959a4a34f9f702d

exporter_context: 00
L: 32
exported_value:
7b3df6d62a3a06cb4b6480a42ef60538098d1805028a1359ed3c1127e65916bb

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
3a72f71ca5dbc3cdcd4dbd5f8d708ce86a5e29344e3312601fbe855e91a87646
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 53c0b6752f3f2dbbe8ac55c4a1b587015a7d21ddc01bffd89afc1d44cd97d346
pkEm: 5454c5260010dabf0e4e9249ab72d18720a78cefc95767dc6ff50866cd114367
skEm: 5cb58c132f7c3974b02565f7891c42b9e004005e6e55c622f09ef965f97002d2
ikmR: 90895b5f9fffa6a5d35ad8065245b0884b2ee29381859d23314b8f96ef8096e2
pkRm: a74cad808d6d3e08f64822a3cf2c580af58165eabf5303d84c7b53395d5d9e7a
skRm: aab730b4af9f1ccc93e286d8722b9e96ed643f53e14b776dd0a91179b806f514
ikmS: 9c85295e447c2ff5535727e975338d0387022ff2e2aa4bcdd0bd74264c9a9f2a
pkSm: 8a868a6e04fc6590ae224a797d961531a4e4dbd04750b90bc7ba01bfbc23e14c
skSm: 7b15094bfc9c50110685379d7bf82204806945c5606088b02a30aa48b600ca05
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 5454c5260010dabf0e4e9249ab72d18720a78cefc95767dc6ff50866cd114367
shared_secret:
b93adf7228788470175c3040ae810cda2abc1f91720813183624a66a7749fb1e
key_schedule_context: 0351af0d3a80f50ff5d606ae45bf724c2f872698eacd389476
90bf75e1262a72a30f0d33c7dafc645fdc165ad9d110e77f68358179ad974a9a9b71dd05
5dec5eee
secret: 3c9a41df3e27053209bb426caa8074cb5fc889957d562252b6c56ddfebf8a027
key: eec366f721e4dfc0e1bce6220baf5c2684c62c94d6b5b8efb26bb3be93acd373
base_nonce: baad2059f32bce708ae76ed9
exporter_secret:
1f34a01ca2e595fdf32f30f6fbba31a4b62accedcff89a2cd0f5ea32c93f2e4b
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: baad2059f32bce708ae76ed9
ciphertext: c6cfa11995f468f98eff3d2fc5276469577b4c222176b160abd37b891347
96161be7e05e021fc3365d60aca172

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: baad2059f32bce708ae76ed8
ciphertext: c5c605f0d77a583a2bea649cd8a5f3d7222b9fb5e06c594a9ca4c2e6dffd
5a6572e4aee8868e1321fe7f5d66c4

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: baad2059f32bce708ae76edb
ciphertext: 27d566f753d1a1ada38ae3a65d801c764678aed5c1a4171dd746529bb810
1ff34b7d1266241889268141699c3b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: baad2059f32bce708ae76edd
ciphertext: d3d4eba5a60aecb5f8d77e3585007512eb5686e6762f52ae28a94717ddff
1f3a4f91c5755907007656b08ed9a7
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
3778da9fca4a33856a9d1944e0bfa70782849a30a6541f5502ead22261d192c1

exporter_context: 00
L: 32
exported_value:
5d67e134b2cd495882c10301a418366ee5e583f6b2da3ade110a050320789dd9

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
27d8d66f5a8224cc653c6223aef70f316cc0d71b6ed3b138f5c0d64f42e627d8
~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 79d2d83a16f454a6bfd9349474aac22f0967407c6fffc082c4930a3f5810cde2
pkEm: 047ae835236ff7416d0c82c566940445ef6811f1fcd281c43d7d70b3e5dd2a87ee
1fead4da9891fa77a778de9d51abbbf48a4da2f223209b39fd3df2925c8c8f09
skEm: 7af314be776a3208b6ec0ee1c432d41609702150663de3d67e190ecab3d86361
ikmR: 4744b926f97e68f95c0327e2e9e795327a374250639f12eaacfeda3c2ed8f32a
pkRm: 047a79c7db4ae5e8408a021eb33f3b7eb5a403eab9c8a3d67129a6c43f717999c7
ce6fc8281252572cb83ae867d980e691cfc46a9be605454456be162e659046f1
skRm: a37572dc4bbd2289f7402e4adb96fa578b4360496fba6d90fd93c4cfb3304ad4
enc: 047ae835236ff7416d0c82c566940445ef6811f1fcd281c43d7d70b3e5dd2a87ee1
fead4da9891fa77a778de9d51abbbf48a4da2f223209b39fd3df2925c8c8f09
shared_secret:
6c2eda81a6162d5504dac08c7f39f97cd8e0e6f51313553bcd84ae7164b8a6a1
key_schedule_context: 00abdc9c4089964f95ca07f84a7d90d1864490d302249bfb20
7a247b89813e9d1e4adacd502dd077a8465b84cced711d5a741aace2f80a9ac865043442
2fe23927
secret: d7d53848fecf40d740ecf9bfbd1efa432cefbd95c2e6a0f97b3a52c3b20ff418
key: 25303fd94f391fd9dfcb6c5e51ee8c67
base_nonce: bed9adf6cbc97adb594364bc
exporter_secret:
f9403b6bb96d90341bdc4f04f0bff288b6f0b6b6884034a303db9fe062e50dfe
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: bed9adf6cbc97adb594364bc
ciphertext: 6503f78afd4bf4e4af5fccc231818c1bbc3f38fcd6fc7c8fa8e1c30c0f18
2093779703ef8d466ec4b471a8f26c

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: bed9adf6cbc97adb594364bd
ciphertext: 8e0f92ecf74f739aaaf42b5074000036deca980625f42ac68bb7a4624eb9
540a38499a48d9356ea92ce242d862

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: bed9adf6cbc97adb594364be
ciphertext: 5d33a722538093172c5f613c163b46ab9f20f1c368b1e1c25a3bc4a10111
5ab0af2f67ad1518cdb897341cd5f6

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: bed9adf6cbc97adb594364b8
ciphertext: e4fc5f33b6e82a09a10c7ca74bc8ef0cb3e62ace55afd935bcb2ec5f2682
5c1968ace275fbc1afe4d379f417a9
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
09cd916eb471d6bc29fe2f08c181a1be9e700426569e1b38a1f12e585186a394

exporter_context: 00
L: 32
exported_value:
27a53846821755b976b7c50fd815d5f9978c05cada0b593d7c3a57b0389a69c7

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
24e87da03e28dd7dd1ecaeb2c5941de64d2f45f13beb1a30fa3ba842dad95158
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 01d8351c259b3db5658c9d39d672e80842412a961aed1c6b652ea851bfb11c09
pkEm: 0432ee60b55e671bd9eeffdc4d9a825a08a9058bd65a716bce217f7c34d69acb44
61ffc70ae124225662e7288fb556a07709eba55597b5d97ab183a3cb9b067627
skEm: fd64c72e5c236f84d9e4aea00b42d2893f7d78015b6317f1ae24012517f1ad85
ikmR: 3ce248bbcdcd2c5a5b6df53663109d141c8452058f37252a449e57966d211465
pkRm: 04f9677afd7328c24b277e46a2b4b71591025ae54f138ddc660e9a214f914c4cd3
65cc3d5128c0523b83ecdfb2002753f78fc63869f05d03d829626f8d1fc512dc
skRm: cbb05dd4706a9a9bfd51986111b47790118681369dce2c78f016d1c7c0950a2f
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0432ee60b55e671bd9eeffdc4d9a825a08a9058bd65a716bce217f7c34d69acb446
1ffc70ae124225662e7288fb556a07709eba55597b5d97ab183a3cb9b067627
shared_secret:
40781ec714f323afead751bf06febb307523988e1a7e1ff67eb52bb22ce936ae
key_schedule_context: 01b1ef02398e702f654bf6f28d9825bef0e545000702cb1839
b14bfe7c754c501e4adacd502dd077a8465b84cced711d5a741aace2f80a9ac865043442
2fe23927
secret: 56c7be30b8a64ba91f44fc8de0dad2376845dc9a1a7f99035db7521f78b9df0d
key: 6c1969443409a6b0e68af8b0afcd6da8
base_nonce: 874aafb90617b46935e4d917
exporter_secret:
0b1b80a5b781154e297d55a50f37de55816ccafbc969fe930a6f2c4021eb1d00
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 874aafb90617b46935e4d917
ciphertext: 1ba6cd207dbdcf824020ad227a3384edbba153da1c047bba7ee3339a329b
a64753a3cb663fc8c6681aa304349f

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 874aafb90617b46935e4d916
ciphertext: 8118e626d51d69aa58af7334c1e29750697517239a5c9a914b77c15550c6
f39a9e4b25cef453202d7e667c7417

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 874aafb90617b46935e4d915
ciphertext: 42103440403c1b260928f9d0554af1cc5915db64d60d5a058f07747aedfa
0ebc169a83ad23df5152bac697787a

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 874aafb90617b46935e4d913
ciphertext: 02d9ab22d935ffbc9e277ff37dec9ffd7b46194ee4e127c84ffb8f9c0e09
776149e230e5a43e2c331e7a2ad9d4
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
d3ad4365c842314912aaa1a25ebab33c873988a29ccf37b22a7998b9bca5ac36

exporter_context: 00
L: 32
exported_value:
1dfd9aec9a2ce4cfe6b374e779aaffc45c94b12fa03c99420e057850b39bc384

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
eb72a0aaf21ac9c2aaa4691427d1322021076b8dd6a602b702120ab8a8c8a84c
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 279aad67ec62f6580be35450c054a96870662def14cdd4aed16c8a2bf4861c96
pkEm: 049fb66e5da6e20c1ac3dd7913c197990a90fa6ce1080de5d7fac4d9413cf003ac
c9b466212d9bd58628029d7d1b6aa7ccdb86fbbde381280f2e3ad654cf1cfef0
skEm: 4f129c59b21e1219081a0da6b7286f43ea78e58e9daa3e2e79e75b7b94b36288
ikmR: 4e0120210f01a7b381bd9f69882c5dd6a1fa44f2552cffaa7af9fcc49bb35cc7
pkRm: 04d725183790f0538d7d6810f1834440eec569923580d4c28665f356b3eaa9a2eb
5424218f0d3bf6b014e9ff4fd92f77be5ea5f44805372c8e97de75a46391897e
skRm: 64cedd48ef23c5e7d681e439b54b5e967bf91e82223f999254bf51debccf67d9
ikmS: 27e3edac55bd0f28bf59846cd9c4beaa2e13ac6c1035cffb36402bfbf876c9b6
pkSm: 043e15611995ae381e284ccf61c61076ade44ad7f2b782cd38424eef20cf2d063e
88f1094c703ecd2528d25667e9cb45b205889ca44016e11ee35b1b8949fe9b81
skSm: b13d5adbe93435eb2c5d6a1d488bd49f3b7ce51ed710a28aaae4e8d4a2efc62f
enc: 049fb66e5da6e20c1ac3dd7913c197990a90fa6ce1080de5d7fac4d9413cf003acc
9b466212d9bd58628029d7d1b6aa7ccdb86fbbde381280f2e3ad654cf1cfef0
shared_secret:
e28d86112eb269a7a571b49b890007e9904dcd2c9fe033a444e95427e215386a
key_schedule_context: 02abdc9c4089964f95ca07f84a7d90d1864490d302249bfb20
7a247b89813e9d1e4adacd502dd077a8465b84cced711d5a741aace2f80a9ac865043442
2fe23927
secret: d06ead9686177146bac7129a6e6dad18f7e31ac79b3b799025c6f522a803d3b6
key: d60b952f899be8a457fd3fbcf9055c09
base_nonce: 138ea25b93cd2b90c7d85ae4
exporter_secret:
f86716f031aa573aab799a7f4024612fa4ce21137e4421ed4001191b803a09ad
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 138ea25b93cd2b90c7d85ae4
ciphertext: bd536a7de400c3a4625ee1537a470c711d30b326993ca053cd4b50445f40
053cd99227968f9754132327a4c285

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 138ea25b93cd2b90c7d85ae5
ciphertext: fa8a26b4004997b14362f26ff88b3f5032b286b0fb79343d12b19ca71187
6845d3e614b266b76ca89ef8169f93

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 138ea25b93cd2b90c7d85ae6
ciphertext: 949b33ff5980a524a85cf350b616c47bbea8648110f242a86aafadd598df
a09e0d50c94009f0553822f7251219

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 138ea25b93cd2b90c7d85ae0
ciphertext: 438a295474745aaa96ea9e3474a99d64e6511d64b5cc720653d54093dcff
07e3febc765ba4f3c392e891e6c0f4
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
6cbdcc15c12de101233e7f2b536bbff04c18bc06c66f1186241d8cafe1e5a912

exporter_context: 00
L: 32
exported_value:
726558927ee48eb55dd916e6c843674c08021e7fab53c51904418cfec8304968

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
f0f457cf7568264b5194f5779f1f0bacd45e91753c8c569a4606b1d2dc73a89c
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 5a20a921b73e89b7a2c61f9b38baba01e22c9c899dc69688780bcfb258c8471f
pkEm: 04648cd0c3a17cfa2ecff1e8cd9e34f3d4b7abce18508eaf5321cae79cd938fa3d
1321585863b625a35627ab870cdf01b143e342da61653d64bf2ae44fdf398118
skEm: ea5a59ca3f0cf163a9b6506672c76495cde9b65917c194310212189eb7d6a43d
ikmR: c261994d11552648a56d026ce52bba682591bc3e636490387d2fefd9b97474d9
pkRm: 04fc3ed189116aa099c0f68e32bdbdf6a1e129f8dcc3b505c5baab5b83afa4f896
3d4e785246f244126f3d036da94ec5cd43e00f311498fa2346672c981c0bb420
skRm: 767a711d684bc8171f15057e883ccbb6bfc13734244d77f757dd6027dafb6e35
ikmS: afbcc7aaee66a5b9a7fa23d98e383ff9bceb16037566bf9b525aad8ad950e21f
pkSm: 0463bc3a2c5654773ed8119ce7786cb140ae7b5e491be4b4f552f8665c58cf86fd
e61d48129150ddd0971739ee5f2665385fa51a13c5ffdae7f2ce4d99eba5678f
skSm: c0f98c58c246ae01b000360a3082066edc6661bbe914cfdb7b4842fd05a23e13
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04648cd0c3a17cfa2ecff1e8cd9e34f3d4b7abce18508eaf5321cae79cd938fa3d1
321585863b625a35627ab870cdf01b143e342da61653d64bf2ae44fdf398118
shared_secret:
97eeacc7754667248ee03638714263814477fac6f3d3d8f852214e22fed8dc5a
key_schedule_context: 03b1ef02398e702f654bf6f28d9825bef0e545000702cb1839
b14bfe7c754c501e4adacd502dd077a8465b84cced711d5a741aace2f80a9ac865043442
2fe23927
secret: 8f99573df23eb6d2785c809148355accd38c5d26c76d08a9fc8fbfdb6f0c0626
key: a3221039263c01ef831dcc11b648672f
base_nonce: 16cf700b204c586c3fdf6217
exporter_secret:
c7796299e510155d5e887b900e073089c5d07d177d1d64a1a6f52045bf7dfa47
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 16cf700b204c586c3fdf6217
ciphertext: 33147fce569e9410698ab6ca337716a2407cde083070d0d0f448df80ef0c
6d23861a8ffbb665a7000064d5836a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 16cf700b204c586c3fdf6216
ciphertext: 6aa0d147f58e3cf30daff507f7ff81e341af57ec5a770b11b378bdea8ed9
d668d28c4decf9b731244638357b41

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 16cf700b204c586c3fdf6215
ciphertext: d00a5972e33dbfca4270cba72be0c9b06bc7d9220e16babbe8568fbb8e2f
ba0465960369525d90387168d6b13b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 16cf700b204c586c3fdf6213
ciphertext: 2d6bf78b361b42ac84a96e3f7ab8961a735fe27ec1497b056b13576dde91
1ae8c76ade76a1b66ce142c05d11ff
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
00802290555af46fbb1ed451ac579a21ff9511c299aee8a0aac802fac13f07d5

exporter_context: 00
L: 32
exported_value:
6b1361605e2a0a6f7f9d2c8a22a3fb9f6f8119726a016d6a745300cd4c172eb2

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
25f8a35a983ec17aa574ba85d3948b8d32e36dc652511d043fe343e0aa67d9d6
~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA512, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 1ee5a3ff546b36ed07e874f7a742c2eaa88251c528505b0c7c62ce9900e479d9
pkEm: 044e6981275e0a798a7c4fcbe8bc074f3dbb19bd4c2c0da798bfb73f31225f7797
a7e1664d9112587b8533475ccad4cfcfdf9d1e49ddede155a4369bedf20c2ed6
skEm: 96b32d743cc86127641db89b90fd9e9485f68ba854a29d5946378af37def61c6
ikmR: 4294d45c36046a97f3531d9b1103bf784fa34f2e511e273ed24fa42adb4586e2
pkRm: 04ccba73d220aef74342fbfedab887858e60606966ed243f96b7deded13500ea8d
5e16395dee6efc599adda787c8b110cea6550a658d9e096190b4355cebe72b14
skRm: 08bbce16e78cf1cf0e98c70ec76c44e727874490ff1afd6a5eb47fc53f99f6da
enc: 044e6981275e0a798a7c4fcbe8bc074f3dbb19bd4c2c0da798bfb73f31225f7797a
7e1664d9112587b8533475ccad4cfcfdf9d1e49ddede155a4369bedf20c2ed6
shared_secret:
c8584ad2650e3bd13bda253df90675e84fc8acb761f3eeec717ee9de07012968
key_schedule_context: 008bba5aff4a4a949c4caaf55df2daa905f5946efb46343832
6fb2dac8504145236cccff5a2a6115fd54f5fcb61614d951a1506b918aea54eda6f60967
8f4c506f0aa4844da0eb89cd2aecb3dd959e4e33cc9a46aa8a7aaea199f4e99149ac50b1
a05cd20c970376cfaa5e61479dfc4f1fb4d39ba794f274965065a79536faa517
secret: 8efd6e199a1358f116c78075c1c0866cb3e1ec5827d994328764f2cc9044bfb4
d49889efb742e59899e7328c91b26dbb7e008a6379742bf4c34427e23819eb4b
key: b6125bb0ce0ef76fd1afa875ae90f63c
base_nonce: 743dcf8c301c935e0b2ba744
exporter_secret: a11f491bc9d08fcf9cc751b35379727b22cdeca152b3cdc4c568696
287f447e856f0c248dab13ebbf9b38e8c3d2e65d51bdd00a5821ac6b84bcbe78eda78c4e
6
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 743dcf8c301c935e0b2ba744
ciphertext: 70a5be9acbefd091bb113d03ce26d67f7f06c12cc0b9b0d0ddafb9623011
447332433518264616cff21d4e569a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 743dcf8c301c935e0b2ba745
ciphertext: 3b8257b82342f80f20a6e59d4405bf93cc1d32632e64b77daf4b71b57183
125c67ae0957425d1ac2c2296972f9

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 743dcf8c301c935e0b2ba746
ciphertext: 77806174db0ab0caeb12a4bd18595a1b36f2986f5fbf61f795b387ad86de
15c004ea66699e7bbe936e0536fea2

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 743dcf8c301c935e0b2ba740
ciphertext: c541870894c94964bc145a60f624d52578816e8de880543555d0c3f24b35
612f736b2223134b6f111d31e5f0f9
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
56a47805ab663464be4c152f0724055e423559cd7f9b7e4fded9ffc6cdc84b22

exporter_context: 00
L: 32
exported_value:
3569f4f49fa568f8d795e41e6fe060d404e06cf67a19bec0c4e4a1fcaa57130f

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
0629df0c626d6d8c8820fb64c7366176033690b4ae9dfa30ef16872da0a9eb78
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: c2f32dab802fcd8204ad80177c80a13e3a7a4c496efcf97af12519e2a50125c8
pkEm: 0413979120bbe4ba3c4b3ff361b35901d95caa78a729163ba273901f50cf54bef4
7cd0f4225244db68d94c75851ff8a73c283a53f5ea65e433aa399deeb40d16af
skEm: 09e6bfcbfd31646553b9135830ec7f42124c1e3a69c662bc1f24e839232f16f6
ikmR: ac521cb28504afc37fa876ffcee9bc0baf0462466bf149b38bf8841a9cc211b3
pkRm: 043eb35047867f601c30e9d448e9a6695e6eb59cc977103059bc7fdc5fbb4ef13f
e24b85cd2b182ad5509bd3c19fd2bc9aa15d008f8ba464a321320c3e7abd65d7
skRm: 922be0c2a667536844a0bc86b9a5ec888641b4be4290f73f3a4e53d97d3f586e
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0413979120bbe4ba3c4b3ff361b35901d95caa78a729163ba273901f50cf54bef47
cd0f4225244db68d94c75851ff8a73c283a53f5ea65e433aa399deeb40d16af
shared_secret:
631c487d991a270a916a75edd3a481797300df65433222363e84b20254ca1a19
key_schedule_context: 01f37d94392114a83426ed4ef40b204fcabab8c86d1541b7dd
7f71d1b09337e947844179d92df0874ed2232caaea0079bba932bb2369afb9a8ed2832c4
e0d537cc0aa4844da0eb89cd2aecb3dd959e4e33cc9a46aa8a7aaea199f4e99149ac50b1
a05cd20c970376cfaa5e61479dfc4f1fb4d39ba794f274965065a79536faa517
secret: 7ed04c5832e2ba8a72e38a1ebe8b899be25d0cd4cf03bb1f154d2e02be86a2c4
a18af98dd25540bb1c4147d74f93a9d5c4acda5d982f88fc052d7a2871332fe2
key: e407207383e9d8ede15a472aed5f9730
base_nonce: 9a76e8c533bbb6212a00da4e
exporter_secret: 3944e426ad160eba05f7b8ed75eebdb04e3a412565c1f53d1d30912
41673e583565b18131282f27e5c7226b558393f63484c9b962bd98422bb84a5fc585d67f
1
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 9a76e8c533bbb6212a00da4e
ciphertext: bd952f2a323ffe8dd12e7cea2662f5e57d3a66ece18a501790dcb0612dc3
c0a1b60fadf4fb8f7a1088b04ed496

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 9a76e8c533bbb6212a00da4f
ciphertext: 838680a399deec4692cfbe24c2918a17949e1b25132f52cb4a9de97622d3
87a7325e1213388d03b856b3f59564

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 9a76e8c533bbb6212a00da4c
ciphertext: 246ee8905326aabc0e694fc22389e3cccbae4ec8d28b49f194d126f3efd7
63270dd6294a4470125642907492e5

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 9a76e8c533bbb6212a00da4a
ciphertext: 751ad33bcedf0fc7bb81619087c4d3a98e3e8a30f6c437498df168f29ec2
fc101952ed99b7c3e26e8bf73681f1
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
a96b3a0e5acb261e2f7d6c6a0f6335c985add5115ca8da514a652d4e63a68e24

exporter_context: 00
L: 32
exported_value:
d4a8d18d0b0ea73d50feb7deb35a85b4a7af0fd78097c4010ffd08c892bc3316

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
9cbed211fed777eaa11a183cdb416f2eb18850aedab513bcbb4f60d72930d842
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 362a051bfd892d2fb30ac6ceeea5dc3088a1c1c1a1dabf0ca9853294083c92c3
pkEm: 043f71abcc62d9b4b4cfbd9f38c4ffa764b84db130bb2b6f14c623ee4f974bbf54
4973aef9b1b315fc62f38593a48c9a0924a5f4ee7ed5a373978f4a3bb670de49
skEm: 1c2bcebbd1da08293ebd1f86a8859b5106d66ace426ea6de69e9b6e6ae1c380a
ikmR: 2789ed3e856fa74b7d7bb6b8972ede7657bceaf88e7bdb9a3b38c6583eb5ff24
pkRm: 04cbeb75069609f39f1e1f4de7e7c1bae75594441695be2f05e1d1fbfa4aea2eec
700fe1bc778b0d9f765c539ebbb7b67c6ef0b879381dd955a526553b964d4e31
skRm: 82f2875846805d23030234774d0092fc02ae4217e0d81349ccfd6fb65aa0ae81
ikmS: 4c16a0534ef1af7d0b26024ea9ee51d6048e3ec83878dde32eb13eef9bfadb29
pkSm: 04c14237750cba8de2397d6f4870cf7e5d9424c903221eca82a358bed6dcb0b862
358f3efca00d52ba569dffadbfe48878b7c588d3f915d7233ce58e3e61d41f10
skSm: 1464bf6ce760240e4fce5f0b04802bf7684a62726d0d865c3c8410def1693156
enc: 043f71abcc62d9b4b4cfbd9f38c4ffa764b84db130bb2b6f14c623ee4f974bbf544
973aef9b1b315fc62f38593a48c9a0924a5f4ee7ed5a373978f4a3bb670de49
shared_secret:
c1f6cd32245c3040d86013fe020cd3152476b6f9d77afa1f588e805163a0bad8
key_schedule_context: 028bba5aff4a4a949c4caaf55df2daa905f5946efb46343832
6fb2dac8504145236cccff5a2a6115fd54f5fcb61614d951a1506b918aea54eda6f60967
8f4c506f0aa4844da0eb89cd2aecb3dd959e4e33cc9a46aa8a7aaea199f4e99149ac50b1
a05cd20c970376cfaa5e61479dfc4f1fb4d39ba794f274965065a79536faa517
secret: 40d33eb27d8792722e3c6bbf4af985c3fab6f56adf438d196d560ce40ee6a982
3fdec84743d3028e087a51c63f902c6933e5bed572794eeac14271836eb781b9
key: 2ad099016faf49345e4b5da75743faaa
base_nonce: b8ac2c86d66df2be47084cb7
exporter_secret: 2d4195bec888077b808b9253ccd1caf900aa667eaf2b089c48e41aa
645c49f811851b7822f00241d0cae55b78b5bb632b824322dc6572ad89beca25b4d58a00
1
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: b8ac2c86d66df2be47084cb7
ciphertext: 7fb48ed82b1462d07413d463ec39f270507821fce5e4d081bf5fbeeffc28
f02e4e73ffc5a9c8752782dab7e31b

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: b8ac2c86d66df2be47084cb6
ciphertext: d4e4faca01e6696f9f7124f90c91595cfb9e8412d320ccf6cdc649552d90
891af86ddb0ebd4ed19e9a82e9a8f7

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: b8ac2c86d66df2be47084cb5
ciphertext: a297723b8a060b45b3915ea7bfc60c06459b847a49e199001f08168cd3bd
1342668c68e81eca5ed1b8ae2e74e2

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: b8ac2c86d66df2be47084cb3
ciphertext: 77f1ffcf5a5799599fc23522e3c3393359b4d8145d4606467126637079f7
99cc217f148c0a622d21b19a26f85d
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
476264afd67fbd20b6544e03ce478fa145e9ac5cc03e37e7afbff535001c2c63

exporter_context: 00
L: 32
exported_value:
57657461476db163b3421ed53afe9960ed6cbd90207e674b48de478107dbfec8

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
b8775012116da564bfe5a6f649a30a8c335711f836450f8cefea1050acb15d80
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 7697e91f81d1203e746c2f6a9c9112657d256d1eb0c214d50c7160e8fa5e5028
pkEm: 0473df13b40a15d9e34715ff663757f6989b60ab1d2685ac24284015ba59b76b53
4cb0aac205211041603d131ee8aab839d7d8f1f2e1664d109d88b0ea38f62752
skEm: 6daea1e3c63e8feaa3362ad6bdb3e72a4e745939900cb88d41471830a0a6ca24
ikmR: 3e0ee22e5072edb997bb2159950ba2fbe69c005907ce444cfca2e9c6eeadd88f
pkRm: 04f367c7dd71dc891028c7c99aecb70b96040081da7f64395e6688071eed4862a5
c1a63132404d3ef2fbbee84e83fecfd6a499af965b37149181cbad73d70ccea4
skRm: 7d5ee965f23f75bd26d2bdaca511e3e1c06440b706731fc5f2bc81f2c93851f4
ikmS: 01f8a2e49cfe8a53e1bce9a036d85fc6dd65a0415c8a46c998e75ccb9cde0dfd
pkSm: 04324d26cba1490dd43ce5e1b9c6b9fbae3a42b22025a0b5d7bf7e5a3097784454
8c2331d25682769aad545da22de733412b768a6ded626f03e19f87ca03fabde2
skSm: b72b0f2f0b4549eb4a388e4988ce8bd70598fe41b69a74b8705f6f743c17637c
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0473df13b40a15d9e34715ff663757f6989b60ab1d2685ac24284015ba59b76b534
cb0aac205211041603d131ee8aab839d7d8f1f2e1664d109d88b0ea38f62752
shared_secret:
befe3a4821f6b6f2329834db5bf0b1f54cc33abaa74e7ec25297091bff6027b5
key_schedule_context: 03f37d94392114a83426ed4ef40b204fcabab8c86d1541b7dd
7f71d1b09337e947844179d92df0874ed2232caaea0079bba932bb2369afb9a8ed2832c4
e0d537cc0aa4844da0eb89cd2aecb3dd959e4e33cc9a46aa8a7aaea199f4e99149ac50b1
a05cd20c970376cfaa5e61479dfc4f1fb4d39ba794f274965065a79536faa517
secret: e7463c6d2fd06d81dd65dd412eb97411be5790ea2d0515fbd0209e032cef18a9
31c1a798b83ee48bd321484cf26d4a72d7052f453b7e9c0d67f9a830a0b62da7
key: 9703ecfd451654830fcb5d93c6b209b7
base_nonce: 1d196d6fa6e6b9a123cf29da
exporter_secret: 8231fe3f1ae43858df4b32d1f29ab5d13b286bdf92ec728fe51afb4
996f0d3c8202f3ea94e50ef0aafc0eaa89b5754defd08ed7a12ab3a015ed20f71d246a23
a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 1d196d6fa6e6b9a123cf29da
ciphertext: feed88b5b9ecc9b8ee01bd5cf1cd78610a5d0f3ebe1731f8102b02971e27
ada2a280729504687fefb89ca65193

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 1d196d6fa6e6b9a123cf29db
ciphertext: dbada482eb4f1b63bd8ac264f88663c7c8eb7e1499983fe03e98e3fe56ad
68b10a734ba695bdc6ebc67f410d24

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 1d196d6fa6e6b9a123cf29d8
ciphertext: 105d0efca91f52409e4f3d2035a9735888c9c99135fa124ca0b3b93e40c1
67324afddec740b5528aceed0bc114

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 1d196d6fa6e6b9a123cf29de
ciphertext: fe5edf73ea0854d3e7a9881dbec661216d62cab80a53473d57d6ee59006b
3150f322603b96e643d986cfc50704
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
142513c86fce964e2704f32f647dcfcc59f4a573ec686918597c58712a556f34

exporter_context: 00
L: 32
exported_value:
89e37ff1ed631dc641970fe53d8d573b34c99fbc2df00f5651d518dda3aea10e

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
510fdb6e0d17a2006e57410910ab72faf9761cbb9a37870103c9bb4300407992
~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 6d12f66bc65ddb1309339c7c4a181b233e49722f15c5b3291a499908c3eabbe7
pkEm: 0429a17cadd0e7ee98f50e977bd4dc7b28cc66911940e596b71d2de9429e7f67ae
f82ac0227f363825f60a2c14dff818a41a9f2e139bbdf91197cda29cee8c4c17
skEm: ba00f15fd41016ee1eddde889cfea02772bcb81c65a9ee4da6947260b5cf3e28
ikmR: 5c0ac1e1c898a2651d9c796012a1a929675a9cc1c4f7b52929ac59fe7819e065
pkRm: 040714fd5a54168e3e6cf20d937e52a9304f93257d2ed9d425ad529597767cb2ad
4aa5d1d5977e46652a872c7aa203fc8632a7788b210b4cf903062e2f17af50a5
skRm: fe8cb0454ab33b748f97ce17bf14982ec211d2660ab670056847877e137129d5
enc: 0429a17cadd0e7ee98f50e977bd4dc7b28cc66911940e596b71d2de9429e7f67aef
82ac0227f363825f60a2c14dff818a41a9f2e139bbdf91197cda29cee8c4c17
shared_secret:
b444f805efc78ab39d6b363008c945bec7b15db8db345312eb0c1bac43397e7c
key_schedule_context: 00f1c18fd8da4af5b3ba4b18ab1b66fc11804d8e56de307dcc
375c6c528520c91eec1f66cc97b192a4dbe73c73fbbd95df11beb60644bac645bdb003f9
3eae1438
secret: 88f80e9e5608dd68273d882866d6c66cb45e8c8899bc71632af3fae0ec729101
key: 110926b4f39a6ff9288084d2a56d74065c7fba998bd263ba23b91a1a3f6d117b
base_nonce: 6f9bfaba53044d1ab6e708e8
exporter_secret:
9761a07f58d0fd1b7fe74ebe9c7b1fc0a92d7bfb56af5374452efe52f4970334
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 6f9bfaba53044d1ab6e708e8
ciphertext: 06ff95a42fcb9126e1899bdb3901217a229c7d3a7383b4529e5ecee813c3
9cf3e6638d8b7a9c8815948d770b12

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 6f9bfaba53044d1ab6e708e9
ciphertext: a7f87334a01cb1a7687bd4ce92e09cb763f33fd12f2cc2bc60c89c11fd8a
1cece97881a834015f8103e6519090

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 6f9bfaba53044d1ab6e708ea
ciphertext: 8b03986832b4e087d97e10bf818579ef3009126053f1e6e3381aa73d67bc
a78e87e0c48e511ef59e2f29d5c216

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 6f9bfaba53044d1ab6e708ec
ciphertext: 55d84aac7b335a51a61d196b1f76e26b47f0a158d0c960b9c9d8be19ff2c
1033903bd194dffeed45eb39ffe10c
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
705a0e405a3d2265169902ede285b1265eb861c6291d52291c2336c6038e3d69

exporter_context: 00
L: 32
exported_value:
a8f2143298f1b7ade5f41726a1e4d8e0836588b4f5ee72f92d5acaa7a42d10df

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
8139c7c90f30fdb4c392df4077dc88250b82c2452229d9a9cdda29c9ce7b2db9
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: eb39797c3a149b859027aa71bfb7ed3676d7b3aa30908c4c3e8d80be44dee73a
pkEm: 048ed2c8d516822a1f9cbfd52c072a6779c6f5e19f974015debc154e63c689fe68
acd8ff6e5b20cd85bc5a6efd0bc1b1401e3f34fadc4bf63403b202bbe6acc848
skEm: c5420f1f6e18c687eeab315abb89e2ebffa552d2abf8733bfc24830b9dcc222d
ikmR: a6f84c2f82b9794114dfb8e8d5f513f86016e4fd949c51d79b94a1e00880949f
pkRm: 04d4ec43e12fe0bb5055d72ca99064912c285f0abe6075c91232a90d4ec04c14d1
47b9bc433d1e0b0337f9989985677b5a2ce7e12908d0ffdbfb2aa2effca0b035
skRm: 853d71e9c98498d5fcb06c991022effd7e62a48bf7d8985206d98dc65325cfc1
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 048ed2c8d516822a1f9cbfd52c072a6779c6f5e19f974015debc154e63c689fe68a
cd8ff6e5b20cd85bc5a6efd0bc1b1401e3f34fadc4bf63403b202bbe6acc848
shared_secret:
3d80cae03af60d4b8ac0e91dfea15eb4d7309c5c7d5fd5460a7eb0b530c1665d
key_schedule_context: 01eb05e31a1def4df3a3750746823861cf1546335001189fe2
870b59b88ab18eb9ec1f66cc97b192a4dbe73c73fbbd95df11beb60644bac645bdb003f9
3eae1438
secret: 49a96a8b358c9dcc74fce72430079a105d26587359448d6c498fbaf27fca266d
key: 537ad224936d645ccd0efeae270ff24292a4ca07f3e0ee41ac134434e12acc09
base_nonce: cc70be4cf141901fd9cdc2f9
exporter_secret:
2746c403f30e93d2890bda7c8b8a0a6f50dd8a33af1a34cb6875226728c1b503
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: cc70be4cf141901fd9cdc2f9
ciphertext: 70319429e0bbc5a1c46fd340f03689f8b0889d3f85a222954b5cdf46fed9
aedc8899e90e83890642bd7ca0672c

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: cc70be4cf141901fd9cdc2f8
ciphertext: 1fd7343048eab9c59d4bb5dd8bba8e637fb5c91e18aba6be52713c8a2f27
94f04a51a490a0c16f4d647d47525d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: cc70be4cf141901fd9cdc2fb
ciphertext: 3d9b7d1a47bdbecfd80334014d5e7de6b8ee1e9b1ed0d7e5b00662d645d2
04753a413c2fc256cfef98b524cfac

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: cc70be4cf141901fd9cdc2fd
ciphertext: 733aae385777a8f7bf97b6222495caa0af24b66d31fcdb68dabbd1543949
b8edf7c41c7ca815fe70cead7fdd8f
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
3a69d9234e6474465acfd8e912f71015379ed4f13c1919bdec0f89ffdf1020ee

exporter_context: 00
L: 32
exported_value:
336dc461825ccd7548b184c83889215a136afdb073c3fce684b636a2d664376e

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
bbe38773692e00ea20044df69d8ae44bb1a1cb4b17d223ad563db9c38e9646e2
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 74dfbc8cd5cfecdc4b08bdffb5534d66f318a53a7effcb75a5db40dd5fa6cdf2
pkEm: 04dcdc775e81e53a8b290f3103a22fadc29bbd38947f0bf8d75fddf830f4424658
0d9ce804d3d6624b9fe17cae72bacb98e25b45383795a6f35c452b3dbc540676
skEm: 73751649da082e4bdff8062e46d78d249f721d3cce7b71b41a9a0fa9c21d523f
ikmR: 3820c7926e46e052e61d27875299656219caa5594a57954b6f2516f133f42807
pkRm: 04b6fecd477505514101bb6b4f25681d7d2e47ef5bc085f49851826fbf5bee364c
60f00faf7a9bc3df2e6c2b600c3400c33e893ea93f66c7bb880a7cf964a70c8b
skRm: 2bdd5e1ead44335148ec2fcf149b997d4b7d74f006d66452c11061aa7fc6d4d0
ikmS: d78b248b707fffea80ac6c5fdce5dfa39f165803836c71dd98c18955826e5ee8
pkSm: 04ded094f8e40d119afe0ddabf1be84ad9b90388ad9b005011b12a44ce724366f4
c4d8ba7fd1ab88c5410af63ba19f7766e5465233c1ccba864b49068feeca24b0
skSm: e0d58cb15381cf4b4bbae33afc246c9bf4cdd4f5945a9f0979182289cd4e0af9
enc: 04dcdc775e81e53a8b290f3103a22fadc29bbd38947f0bf8d75fddf830f44246580
d9ce804d3d6624b9fe17cae72bacb98e25b45383795a6f35c452b3dbc540676
shared_secret:
6f678023a85c86fabeb682ee38d2c7dbf220e3bd9535039b33502c67eeda14a0
key_schedule_context: 02f1c18fd8da4af5b3ba4b18ab1b66fc11804d8e56de307dcc
375c6c528520c91eec1f66cc97b192a4dbe73c73fbbd95df11beb60644bac645bdb003f9
3eae1438
secret: 0414199447275629e03a263df42c2d7550bda4b16b2a1449019ebe5e481e0ccf
key: 0ff59446ab356e9d128748393c905eb6d4b202ced52014c4d411308cc7019eb9
base_nonce: c7d115f2c72fcb757ab4d96a
exporter_secret:
427fa53f1ce643a6ce9a8820dd5c63a9ccff5d93851345efde94cfd9430fffa5
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c7d115f2c72fcb757ab4d96a
ciphertext: 26cc3b67308036449acbe06237ecd5bbfa5b63122e1df4af195a9bb476fe
4e867c34610876795f3e871019bc39

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c7d115f2c72fcb757ab4d96b
ciphertext: ad7d026c3b1ddc9add5bffd29b47338728c46c6428c6f6d853890bbbf672
9339b305b07e26139915e636a96e30

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c7d115f2c72fcb757ab4d968
ciphertext: eda1df4e790d370fa498884ed9f51124755a11c626b2bffacb3a6dc0591b
3c66b6c5ea993e7e4c5baf7187337a

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c7d115f2c72fcb757ab4d96e
ciphertext: 18b5fc0c6f8a2d53e8dfbb3683a106c8a9c8c6a313ecb6bb7681c8fb0dd1
007f9b36c9a090f97e8b6a8cc1ab39
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
f0b84798436f486f7452edb8f9606c68a21df54ecfe89a675c12e3f89fd7ab0a

exporter_context: 00
L: 32
exported_value:
6c65446451bac3cc7e8308c6aca49707542085a9c83ae2407b77103c23d0756d

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
bb37ab3fba586d41229903db4462a5cc13cbbcdb76a2f05a017d8c02c6095882
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: e21e30bb0673e171bbdd5a8a65ca7768607812b87d0796d76bf8c72ec833903d
pkEm: 0430387c99b89d36a34444cb61c13e70f24f5011d093c16ccd01d594eee38319b9
ce19548624a6ca039642f41fe17662eb8a1435aa5939280b0f68105c3aec8ac6
skEm: acd2625c29a0f06515def9f9613a7442b8e9d06429cd21f462a708d58e6a9106
ikmR: c9b6a3aaf9b6e0d3a4feb16f667f9192d1e4ef772c66c54782ce58013009046c
pkRm: 0455eb5dbf300d97f5c178348b8fd4a8812c2ca5049a52831e4e05042471eca618
5d16b1f8d644d51e132b035a5197f7814ba4173c660986916ba5bd01d49d24ff
skRm: 7a385c10f6f526b5352e09841c3524f700e8092dd3b401c0968b3be1d11d2837
ikmS: 5cf184e1d23cd0f664d415e5dfe8e5688acd661160820e838b934e01af9c7b3d
pkSm: 04f4ed89f9b59ccc1f7544c7050f69e2218feebb58067b554aca9543375651b6b6
69b84e57296815ac20253ad6bac24b2b2ec58f446fe5bbadea7b09ff12ff38be
skSm: 5e6e9e5533957ae76fcd1b66b537e8764af7ab611a1d07d2dde8d3d375579666
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0430387c99b89d36a34444cb61c13e70f24f5011d093c16ccd01d594eee38319b9c
e19548624a6ca039642f41fe17662eb8a1435aa5939280b0f68105c3aec8ac6
shared_secret:
78045544de8f80fa1b6c9d527c338bd7c0a95ec772849f4ce0597e25b776b2f3
key_schedule_context: 03eb05e31a1def4df3a3750746823861cf1546335001189fe2
870b59b88ab18eb9ec1f66cc97b192a4dbe73c73fbbd95df11beb60644bac645bdb003f9
3eae1438
secret: 94ae3cb40cb826a38fb167eee8b6850a33f0f1b1c8f77b298f736d2909738c7e
key: 05d9982ac93e286d8e340a82eefe2f53c80766d5a6a136a95577a17fa12df150
base_nonce: b2c0dfa7478a69b13a34fb29
exporter_secret:
f9ccf6b97668a2a7ac5274c5e4dd606a3a47a175ad24c9f007feb470ff193df8
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: b2c0dfa7478a69b13a34fb29
ciphertext: 01f9e28c1b22e73388371e53d8d9f6e89168ac6f9e8383c7d0ff09b885cc
13612c976f6b52fcf803952bb3c2f2

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: b2c0dfa7478a69b13a34fb28
ciphertext: 47257d0a2f240ab24f4be9238c71586947412dc24b3ec6452109ec4e9039
aa6cb4900bb6166afaee3c206cba5c

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: b2c0dfa7478a69b13a34fb2b
ciphertext: 40645801318e7f2bee06bc1c56c394af74b23d01f6f0c72ee00e2188dcc7
b01032c6ad9a9e41d45eb25c118c7c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: b2c0dfa7478a69b13a34fb2d
ciphertext: 1306186f7c086153f47e6678605bf2a28d0a7f93689091cdddcb53f18a88
d7e5efe55168c8849e757fe1756b38
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
a7f6d11ca93bbc60379931c2532eaea068e6409d46642bc6c8584e0db2d8fe70

exporter_context: 00
L: 32
exported_value:
fb6bb9c47bb6ae67ee66925c700d3a71d7279b8373debad60cf22e492a336f4c

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
6f994a447be78c4f31aba1780b7e4cebda01ef3a8fbc47c1a7b6f633ea031639
~~~

## DHKEM(P-521, HKDF-SHA512), HKDF-SHA512, AES-256-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: f0c0ac5c509971621d328b4c58e878bc8712281de545f3aae03464b99158281b52
9f4d158d81693f9942500a66ade66bec21ec09e3e1f9e418318dc443851f58b211
pkEm: 0400332768098e9a4738ac4163481575222c43a11ece1e617f52e126e6f0568008
eabc90f416d6a46c1611081f402cecb72293d2ed90403bd68d88ceb71354f416ed98013f
3bbc4685ff1f35b13db3b757b2a9f7040c506891d47308a105478fcc0eb88b8a11615c54
8d0ce59725ce8b36067dedbd30902842fa440d7e4200f1953e1fa733
skEm: 007d5e365a94e8856d0791b15b1e6078cc8b2e0805bc3af571a64bb073d985705f
e653af019f708abc6c4f9659851e94375eb8a03e227535d4d6d190a04b0d7e77b8
ikmR: 33a70f210106375e7d5c7a1cf44646a18594f301aa17af8192d57bf846aa1ae60f
38af94a2c938f08e465858f631af596db17287c54b6b8c442950a10d73c4f06c49
pkRm: 04013b7055a941a0d8c541b0df281b2060557a5c16ff2bd18c6a6f6773591493c6
aefff311a256609006080ec7ba9843d360e3fb1f8fc62f1f8c207402f8ced60571ad009c
a550c4ef37e8b8c120a4da7b7eb3bb426ce9a3e6c523af792ac17191ece9abebd66a4c3e
bf177978ed2fa2b95219d1a49fd91f08980c990f00ecb6dd4dd7f203
skRm: 00864345a5d20dd4671b11a2bfd2b3863d866bc4649927648160ffbf1ce744f60f
c33e4b58546e8fe6eec08661e3ccd47126f422cbb919cc1832d1b25a4d6b2ccc9b
enc: 0400332768098e9a4738ac4163481575222c43a11ece1e617f52e126e6f0568008e
abc90f416d6a46c1611081f402cecb72293d2ed90403bd68d88ceb71354f416ed98013f3
bbc4685ff1f35b13db3b757b2a9f7040c506891d47308a105478fcc0eb88b8a11615c548
d0ce59725ce8b36067dedbd30902842fa440d7e4200f1953e1fa733
shared_secret: 3e1aa9531165c858d947ee85a3469562d6f04b0f7eed7db2cd5e5986b
34bcd8011301b3b2d9a580640fe65da50dd1ce9c9d8601e9fac77d075cb15ccddacf4f1
key_schedule_context: 00da5a1a3c5b8143e6db5a30d288a2ce1eba163576d754f4cb
c4ee43552ebf7dd475cdc5d45d9277ff3f7d2edcc13bd6c17f5a87fd01740e4f9d336aeb
b64be9f73b4b7a4cf3d95651612d822dde9365526adc78d0a7d77e570fbf3067ea90b138
e491d673d8666d8e312fc9b576111f058a7678a2ecfbcb0b9c509f3c3707875f
secret: 2a2a18941506cc472c88a1e8fe3b9dd33cc64ed2a6ecbdc14c425c485fea6c09
a2b8449f3f050ae6b81944f93c60126d09eaf935c358a5132d1be9b2e9e00765
key: 441db7c59e74d1deaaf0d2f6ef475376a5f934bd19e664c0044a150957dc5e84
base_nonce: ba97eaa2fce7507b085f9644
exporter_secret: 5246213b345c336c8e4441012059aad26055e303ee6eb5fb042433c
67ff60887a2679b570200efea76c8405660e0f7e7401e3c559d7d534287ce541196818f0
f
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ba97eaa2fce7507b085f9644
ciphertext: 9d5ed1a820681eabe488ef6176cc91a67314e3c7c8e9fea7ddb9959f4123
411c940756fe4ed592b1798fc05cde

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ba97eaa2fce7507b085f9645
ciphertext: 85ae35c4655ec90282906721923e42f25465489b61d1a618600a25bcbf89
41686cea6b62082ceb145f0ecba6ab

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ba97eaa2fce7507b085f9646
ciphertext: 94733c20562326508e54bb267de022f69ddef84ef912c6e83c76f0fbe1e7
f5b36a3569b9a262d0ef800cd71efa

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ba97eaa2fce7507b085f9640
ciphertext: 8c00765f864f44e811ff06aa0817d80ba9e2aa6b2ee085786e71ad625b01
c3b92997519cfe35cf59dac2ea0ac5
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
db0690e2724468432c823947607c400ea5ab04b3ed416c5f96c969de0c642ba7

exporter_context: 00
L: 32
exported_value:
51d4253438a5aa6d80d1d28f43c5ee07116b3fe31ecafb04f4fdf6b14ad7b5a4

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
bb767f8d74135d2354c9d4635af1b499ea36c5c8a044e03a200ceac683083597
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 1fd594e66f3d9e98ec7a3f8d2ddb4c247fcbeb9346248da018efd3bc4ce914755b
c544457163c3863586dae52c947a2891865986523c4d7609f0dd3b50db277bef75
pkEm: 040068acdb7e178dd0e5f7cc61f0ff0edd84b9fcbae7921d7f25dcd98483d77e07
2c7e2118d4bdce84f746cb27d3f4be67712fb809ea3937264a165518fa765d5e94a40014
12c4b3f013bf1b5c60fcb635313414b7a9b9b29e28072bceb55305a582e4ed433fa3dfd5
a2341bda94696a07acf03cd6e535e1213563cdb222560fdda49e281c
skEm: 00616ecb81bdbc9b149c5ceb4605fe296709c1710500117242220d864f64c3913b
bbc753bbfd63e93e4963a9d3625d1139d096d700097680d2e2918598b9c54e17c0
ikmR: 402df5a3285a16f8be63c65a05972849fe8af379fe47888ec077cf3d5f67bde4b8
9fc4bf7f55a48ca28f5f79a99ce529a27291dd8af5f3d4dbbae25611014e788e0b
pkRm: 0400d063d61921b292402aca8e44bd8753043ef9e0476e3b444b5a8999a274e165
3c994c8d98e70a76345c8befeafd9d2d220b6ee25383399dad06f2814a6fdfb8d6d4019c
2d3635722d4dea4e998372ca6c9681f2c93800d5126a08be02934aaa2ee2c4e49b6d6306
ee41dd0928ff96fb4df3c0d5fa604c3a798803802485938f738a762d
skRm: 014b9a33755d4cd3668ddc7d9daed71ff4c7a7f1ae44469cdbd2a3dfac4db40564
d86382dfa6dcc0e0fab9fdcd7c5b4dba291ac3cf2ebfd5104ca6afbb032db188c7
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 040068acdb7e178dd0e5f7cc61f0ff0edd84b9fcbae7921d7f25dcd98483d77e072
c7e2118d4bdce84f746cb27d3f4be67712fb809ea3937264a165518fa765d5e94a400141
2c4b3f013bf1b5c60fcb635313414b7a9b9b29e28072bceb55305a582e4ed433fa3dfd5a
2341bda94696a07acf03cd6e535e1213563cdb222560fdda49e281c
shared_secret: 0d4e710f50a3a71dc965779cb1caf45e5a4e8fe327ef959d378a0e290
4876cd525baf3b880fc896bfdf8eff54f0de23f4cd4a0d42b255272ca9df590b6a31e4c
key_schedule_context: 010fd8cefea7dbcb4870549c1d9aa61cc82348ba99f41333bb
3688fad192a16d85283c8d5041a16ed08480f03dee01579b9f0e2bb7104cc36fce2d8bee
39bc20f63b4b7a4cf3d95651612d822dde9365526adc78d0a7d77e570fbf3067ea90b138
e491d673d8666d8e312fc9b576111f058a7678a2ecfbcb0b9c509f3c3707875f
secret: 6b97b5222fdaf9ea4f59ad3f0349cdd28df81f22150fb9da6169192799b5a8c6
35473d80eea7bea73ece368d2f3a0ab4601f1157ec63bf0c19449d7188a5647f
key: 42d20e50e7c9ea0f115728df9ac8b29013efafd09a9f0e53a23c2129d904cecc
base_nonce: ad5690479ded40c4cc7679f1
exporter_secret: 31a1b66be1ded9622a115ac30f4f2722ecf3470a8eb1c1d03698164
84092a8948a3a55af319d2572860688399f1bb3b099e2b2e53036fa346d929657de0ece1
a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ad5690479ded40c4cc7679f1
ciphertext: 18a8ed2035fe9421a3151161f9cc96e18fc8dbea046d9e08e6a2881a629d
9c94b5735dc4d457cdb6855f878dd4

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ad5690479ded40c4cc7679f0
ciphertext: 849125b293826c222106b0d74c4b20339dcb02331599986c0a695fe648eb
c7864215f90c6db53597b14fc2187f

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ad5690479ded40c4cc7679f3
ciphertext: f9c772efd9c5e54bb5be27a7cd4120fa6da26919902dae26b9226c9270e0
9be6f138c5c954dd6301a26a4c53a1

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ad5690479ded40c4cc7679f5
ciphertext: 3a57a97e089613cc13c1a8dd9205d2ad4d9b8f020f4298fa1302d068cf5b
0b25ff2dc9c42c4e7d203a0d77e1c3
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
92bc199ce837080511bfc2178223e1ccbf0133ce71aa3f2f694fba26f9bbda13

exporter_context: 00
L: 32
exported_value:
641c220136330f31ecfcce151502916fff316b922b1eab5bee3e6aa9438a788a

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
4ef0f29b6c20325b60d0a4f2567fddc4393ca4d0cd3afd2efb509e36929016c3
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 03a5272b770e1510bf34cc0f5b99c4856fec0cc7ba5d70852e521230a2678131a7
e77b7b0aabdac9826afb194ddc32c7a2b810ba19c545a8e9fd97638faafdf49d16
pkEm: 0400fa194a0aa4acdc6d4fc75b9ecfc900b4fd1bb76dcc86857ebd4f0cc13e0e37
1fdda76d5fcc82059f18c6e8d4d7d9a8455eabf678e07952380e4dd54e828a30c4c801a3
027f48a3107622fd079c6996ff71ee887e0612e233c48a01ceecd05f001ab5ec0579113a
0453bade1edc87cb0356383317edbec6783640b9451c17b671286ebf
skEm: 01a0a442457b46bcf059c925f4e15c1d72eabb87244e53e1803a6dbe660db89993
7b144c51466880abf9f16b5a33baba4dc1f5652f1540cc59b4d3bab01d69dfd0ff
ikmR: 1aff67460de09af049cc47698a1a7ace0d145d0efe28141764770c1a0f0b4b2934
ba6036c5c5df906812093f500d9df4686edf375d86814ebea66082838177a663c8
pkRm: 040013346f34b03fa0398aa242e9e89b9b56146e8f6d59e64b8587b26049f31b8b
0669a4bf0c399e6af1f229bf0b74f55a40b64d6f79f7afcf26cf042a71d78b7b914d0098
c8a07483f752a697c49997fcd38736209da333e5110068407b5a10181986eb35ec06851f
0bff7666f82e7a5c301933ccc51ccdbd9dd71cb119d59099acc79bf1
skRm: 0121fcacee5649c694ca80b53c9c151ed69ceb2e0d5a5d9867c616e71f26f3581e
3a08246be8f142e841ed1185f531fb27244971788720bc802ab03744cbfef44362
ikmS: a99661d010e532cd752d14a06bc27c505d712f561a3199bb8f139dd2a16333e646
3f1b6a7136c589d87a1d3e4b5705c83ba882218b564d611cca4fd3e88ae686db9e
pkSm: 04000c1069f04c6ac4c8770ce947b1ed73ab5bc9e97b5fc7584fb150f86bdec93c
5602b7737604ed06f6f9db4093774970d3a075d590749519ccd1e014f5764c002bb0018a
240b1938e4e120888baf9d1dce8d5518be6ceb971388392972129f90a9f840939bbead51
b5277b089f4565be7911568c61c617a88775d69e9d2fa2da744e49ef
skSm: 013a84a8667b6aab114b4f540d19f8eed36cd9baa6f0ac68d8677121f4f72b6050
3d96dc0bc8632100ff23e06f0498249a79ced6fa9d8bc8ed3db73ecf2066165760
enc: 0400fa194a0aa4acdc6d4fc75b9ecfc900b4fd1bb76dcc86857ebd4f0cc13e0e371
fdda76d5fcc82059f18c6e8d4d7d9a8455eabf678e07952380e4dd54e828a30c4c801a30
27f48a3107622fd079c6996ff71ee887e0612e233c48a01ceecd05f001ab5ec0579113a0
453bade1edc87cb0356383317edbec6783640b9451c17b671286ebf
shared_secret: 5a62bf6ce7e10c856fbfb505c070bcf6381c9a507e36ab108a5cd8432
4e7ff951b3ebc1b3296715a868910c58006ec020ab12f63f5004a1f88832f442a45ee5c
key_schedule_context: 02da5a1a3c5b8143e6db5a30d288a2ce1eba163576d754f4cb
c4ee43552ebf7dd475cdc5d45d9277ff3f7d2edcc13bd6c17f5a87fd01740e4f9d336aeb
b64be9f73b4b7a4cf3d95651612d822dde9365526adc78d0a7d77e570fbf3067ea90b138
e491d673d8666d8e312fc9b576111f058a7678a2ecfbcb0b9c509f3c3707875f
secret: 1887186f158172a752ded0071ebf6e55bb3c01202a171a96b31a0922613f852e
fbb2021fc8d719dcdf57920062865789710a59c434295bebf8eb77ec50766db2
key: d8411775b0d7797ab0ee7cce78ead36f2d1ed8940783ece50368878cecc25b35
base_nonce: 597e3c09974ea50b24eab436
exporter_secret: cebf099f8363bf81184b5d7ebc0cb369ca66b34a4c2e4559030fd05
4cafa0023b9b96dbc89b675269a44420f528d174749988c9ba3729dff1fb85e659e2c6e7
7
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 597e3c09974ea50b24eab436
ciphertext: 40146e30b3f264ef1aa580ae8a5f38b848804dc082c3043e757a6c5d4860
0651717b6922a7daaa7b8b647cba7e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 597e3c09974ea50b24eab437
ciphertext: b18a6173d6953b2901eb2659416fd885cb0d0c5a0319d38e5380d2a54912
4f061fc415e5b2a677b566928d2bed

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 597e3c09974ea50b24eab434
ciphertext: 95b9cf680f3e6cb2992824bd70c2042c3c7f2519f7d7b19eec02c05253be
eeef20c678653080e7a54e83b03be8

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 597e3c09974ea50b24eab432
ciphertext: 67288b279190a55a91fc715b814ad0ea495a48a8cd1f2e8e47b9f6b82e69
2c4fd2dc10c952b95c3b1706a7fe65
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
4315e6d1393df0d18abc87dd978917db1e89a9d73ca62f6d054b4f6eeacbf9df

exporter_context: 00
L: 32
exported_value:
7aa13b98a6778ecb5f2e48bd62a3c081c6452109b094c25ea059ab13f4bf5821

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
edb7d3cfec825367fa668cdcba0ec562c07f7604ba113610919e3aaf6db7ca90
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 35497b1baa820c2cb6114279c007e93b3508e74757ea81ef1515703caf476e166a
98fefe4d0013950c28fa534d5a3b67404783e291e7944d93074a4f8ba20ef23eb6
pkEm: 040036e064a4e8e8a2cf27fc5f3f17add5d7a5489b59235890cf437133f74fc575
90a9731d22e62373df5713b9507dde49ea06c09970381b0d8ab9f012faa1d5520dd90148
25b6272d9bd10eb2404141128df0099833036be33c73f3b8a5e4a5863ee186d9f86c22c2
5ec0bbcad52a517c5dd2adf407d5d6ee942be9d27589ac9da3425d6c
skEm: 00d62c4710791d10da5261f3587f0254ff8ee61c9bca3e6ee0fa8aa4049ba72b90
4bc6ddf8b034334e5be44d4274a0a5ed67f8addfb7e94d6512043527c323586742
ikmR: 6a9fced2d337416bc4d6b16a3cf90ce8ecf5ece0dab5f58e29a882e184e3cda8fd
0eab09a8050df9205ca017f1000f338ed31804c8c9f4fecfd7996d27ee871aa713
pkRm: 04003bc2fac87762ab62f8be84b5ca8090a74d15db06b834db5d4fe6dbd146c40d
867a9d50be043d758fe3236ab06ba3d1fca198d6c08a299241cb1bdf9575c5fcdbd4012e
00a28d55b5d7896e6ed3ee2c90173961d2a67821344734bec492e324a8a553ac23cb5fe0
1fcf74dd7c68c75303239a78176aeedcf5c106d00a5760626f0d9e11
skRm: 00ca1a48506f5d9ccbdc10c651021ef91c31c61db91536f1636189f5fb2a0b1580
f735447e39484738614b9228f54b91d9d702b53d64f8f6f06c56b3b497a0cfc277
ikmS: e5e6757aba13ded0f04216f01db84c3c59ac638a9a211f479d29bf779c391b74ea
d87f78a7cd1bd4368fc1235d5aeb145ea2121e3a80be528067760dfc303ba142d4
pkSm: 040133e5282f226d38c82e28664c2133cfb575b65562b373d82d5de4e3bc717833
35dbebc6d36d0941706383cdbe84701d9d70881d83be620d3b4844d86759d1d33ab10175
8c1d0b6db565497b55cbf3dd12f7c4771f3cd23040252af792e10d46df7f43b383545f57
1d460bf06873b3d8c5f98fd301d5c08d223b0383afb24625d7c3ce7a
skSm: 0118ca6b63ed7cf4e89bd5580c33736ac8542ad5e005305b2869da3bd8aa564bad
bd4c2c112bc35becc7a12787fbc7e9fbb763698dd2563d6cc55873283badab20a8
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 040036e064a4e8e8a2cf27fc5f3f17add5d7a5489b59235890cf437133f74fc5759
0a9731d22e62373df5713b9507dde49ea06c09970381b0d8ab9f012faa1d5520dd901482
5b6272d9bd10eb2404141128df0099833036be33c73f3b8a5e4a5863ee186d9f86c22c25
ec0bbcad52a517c5dd2adf407d5d6ee942be9d27589ac9da3425d6c
shared_secret: a684dedb288e882005e49c2c8e43cca78ca71b864720d4baed9b5febb
df1b5aee1d9f8e900262644e6c36ce42a8b3eccff4520595046cab6d57af6b46f2c3beb
key_schedule_context: 030fd8cefea7dbcb4870549c1d9aa61cc82348ba99f41333bb
3688fad192a16d85283c8d5041a16ed08480f03dee01579b9f0e2bb7104cc36fce2d8bee
39bc20f63b4b7a4cf3d95651612d822dde9365526adc78d0a7d77e570fbf3067ea90b138
e491d673d8666d8e312fc9b576111f058a7678a2ecfbcb0b9c509f3c3707875f
secret: 941085e8eac119ed43e5a41ec64934940e580089a36444d9a3dabaa3722a803c
13dfdd42447cf469233951cd4a7c8322b21e04f4a9e33434b0ecc3b851066ef6
key: 0f54d388d5afaab19c7ec106ea563b4f2765b1386950437da4548172fc0846e6
base_nonce: e1bfdfa779a9f9c356c7be70
exporter_secret: a7288c93a3a3605c54cb9a724b76413540d1eedda966bc78a7a9d58
1d6c3938b143c71e921913f0e3c69e6bea7a20936fc7bf75ecb0d422cfa95e3f00f5dedc
a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: e1bfdfa779a9f9c356c7be70
ciphertext: ec2e66502fa0e95329edc0dcd91ccde0b67c886e78cc4722f2b6c190e314
3e13240cf207af35678029eebc77c8

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: e1bfdfa779a9f9c356c7be71
ciphertext: ce8320830bab6ea5ed01049e40bf9a02e8bf4d91372dabf45bbad83856dd
9a1f66843de5b7776dd2fb2a1fddc5

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: e1bfdfa779a9f9c356c7be72
ciphertext: a25a29dec9c6a7c08c2e41f9c0f59e6c098c227a4e6f4cf91afa92f75efd
31d5fa90add7f14edb1e2a8f1e075b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: e1bfdfa779a9f9c356c7be74
ciphertext: 4301e3678b513c2537744953c8682bd75cf147eef16c50d8f5a1d81bb482
17403770aad29a46cf2592920c8ff4
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
09a15fc24a2f94c59d31a3d6e6cc6492aef9e39fe27feddc04532e63a3c096da

exporter_context: 00
L: 32
exported_value:
2faff901285851123f282e8e483256fe3ded686b2f9bf7be6d908a51498af645

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
0b3be3489f161d3e1db890c21e3cd3cc0c5c419c789eb249a0821e58003302f2
~~~

## DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, Export-Only AEAD

### Base Setup Information
~~~
mode: 0
kem_id: 32
kdf_id: 1
aead_id: 65535
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 1396644d17aa9edb08de578c2dfd3d93d0ac0e75d142b8efb7f8b0c1185eb45e
pkEm: a12c0f47f6b72485c745f11952248db72126045e6c5cd77ded2745a14b238707
skEm: ebff1008a79fd8373c4f8830017fb8940bb6c44282ee3d090ced7d3ff5174b0a
ikmR: bd235a80d8ec2bd5ee808b74ab9c31ef6905450230f5093c3dcdda033ea9f58d
pkRm: e16d734b9d11f3ba209fb9d422ace268229301548a9a1e75e5a6761397b0a144
skRm: 83d21904bfc5b0476303f0d0198db9df794f6a92f129313eaaa497a1f65c836c
enc: a12c0f47f6b72485c745f11952248db72126045e6c5cd77ded2745a14b238707
shared_secret:
dced2b10a20a3abaa104f6a8efcf7ffd7746de3f66c4b641b883e9c7058a7cc8
key_schedule_context: 00dd0a37ad96727124b021d7c81c42bfbb68c11f38050b13aa
54adb5a92dd165760f0d33c7dafc645fdc165ad9d110e77f68358179ad974a9a9b71dd05
5dec5eee
secret: e184ca28ac250556a73b7cef239a6b063721937576987d52f46c1366a512e132
key: f2e38546430de5edcfb918ea7dc1306c2f97328d8ad2677fffae3978af5712af
base_nonce: d71b38429ed956c68c894730
exporter_secret:
6837396cf1bbb3ff3be93e14c50397b857ef64b82b12bc91010ae1b413d2e19c
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
b9b91dd605b9a56849cc3171b8dc07188365f733499d204da9c558869ca18f98

exporter_context: 00
L: 32
exported_value:
e00f8263c8641b60274b68d964ef718ef9d9f821875f42f2daaabc1a9ea1e057

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
e7d31f72a5ce1dbaa0e7d8e640d8d1880df6b9ec89720e9e4f1cc6a20e355723
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 65535
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 9826e8b2d506bfc3c7e4213d54b1af04f709eae3146d3cdf7505f869611b1cf3
pkEm: e83ab879f76dcf17c0b9e45db63c06e6b12890b1025ce36d00d5814fa100b27a
skEm: c53612c82147e60a26bae7fbead33b6c1efb63a745fa590091f38080f1712e74
ikmR: 2af46f183f8e807a6377e0871fd849a62c7f85067deb320af344996a1e5e6a62
pkRm: bd5e4029ba38df1942fe1c471908562243836b3db2a40731563ae6304c959d60
skRm: 765885fc6d62fe97e9e005f83ab769f5e32946bc7f8558fc93d9d95362dade2c
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: e83ab879f76dcf17c0b9e45db63c06e6b12890b1025ce36d00d5814fa100b27a
shared_secret:
485aed59c6846c8866444acc83eab75d513088540cf41aea4ed957850930b21b
key_schedule_context: 0151af0d3a80f50ff5d606ae45bf724c2f872698eacd389476
90bf75e1262a72a30f0d33c7dafc645fdc165ad9d110e77f68358179ad974a9a9b71dd05
5dec5eee
secret: 119f205fa5bea22773a46c10ef37bb2437dded2ba74d6c94580475e1286b7d45
key: cf78aed32c26a04f34553d33cb682f59ee4146a907c80ab1d8c71778dc122c4d
base_nonce: 90c3009bed5a3f51ac5ea57b
exporter_secret:
08e73f44ef6116f9c8dec3878f20fec8d225d8e29b9057ea8e50cdc9140f6df7
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
e3554a4787322fc14ad63f96bb72366234ca28f397fd8a791279c75103267269

exporter_context: 00
L: 32
exported_value:
cc10305fdb588775716c9aecdce915310ab5343137a58063bf78815d04851f63

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
ba3a8e5d57ce49490795638607da7d8118b6f4d73e2cb11cb55996a9df044c92
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 65535
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: fca42b2bafffeb05979f344d0c31c8c052a595b775b12634f09c993879137e78
pkEm: 54681e7ef037bf11594be27c9b4e2dce6a8bffbe4b0c52648fff50549491732b
skEm: f4308b0b3e802e96bed51af3cc1826fa395837896b324856d3e7616129e33379
ikmR: 20704578ae50fdc0b49bc51ef38bfc67f38d946d269f8f543251d9d116092607
pkRm: 371a19735f06d1fced8697c51edd81069c768cc8295ec036218162c2f341ec19
skRm: c244aace1debb5d843fa911b10abe56a06767acf48c8e2b1902d98b5e3656055
ikmS: 858cae8e94859318cf29c54a48dec4fa10bfba9637ea7b34e79ddf0bb9cb2f70
pkSm: d84f1ebf6a36061c98f0fc123220b30baed0f994de98d6245d5facad34d8e425
skSm: 7e1fb2cc25e0358613918a3b031fdeaa65f734b3878ffd5a9972e32a55842908
enc: 54681e7ef037bf11594be27c9b4e2dce6a8bffbe4b0c52648fff50549491732b
shared_secret:
8913f39ffcc6b1e172e1f3f6e67ce83959c0bfd370dcf33f5cc1f89f2d5712d3
key_schedule_context: 02dd0a37ad96727124b021d7c81c42bfbb68c11f38050b13aa
54adb5a92dd165760f0d33c7dafc645fdc165ad9d110e77f68358179ad974a9a9b71dd05
5dec5eee
secret: e48ac9c8c26311c080361e93457c624b292c1f9503586bb5d0d959dacf3750ef
key: d545d38471f07dcd59d920ebcb7c5f5c3b77d324c1c6b0a45995f528760403ab
base_nonce: 2b923668b792376abeb823fe
exporter_secret:
8a83fc409ce96cdefad087d328f60a7eacb68c72f082d611a0e502e87e352e88
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
c8a48613162dd0f74f268c098ee6aa499c2c93c7f471263a29844538a8f7f152

exporter_context: 00
L: 32
exported_value:
5a50aee349cdb7df571f58636e86bb35b12e8872a60f9f022c732279c014f4af

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
19b188b970c1e30234d1db6acc9f804712c7e861a9e7b1080ad546e6597ebe32
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 65535
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: c355b0a51165fa372fe7d6f7acaf10595d11b1984940b13b34613c474f9a60aa
pkEm: 988cf0d6b8aa4e4f2537270fafd1eb420d9aa0f1d2f45f46b00b83ce0ed8d433
skEm: a3d63af42445899a3157efb0399a57ff7a4fdab7be5b78ea5af812f67d778d94
ikmR: ed140f46ba0fae07ac733a7d5b079cd2cfdd8df0d4a4676672d3e0e0a83f6f61
pkRm: 574a902e0d214baa9df964c7885d721e099f8295cc59b45866ff2d14b9b3d07d
skRm: 0e61bd27072d57b3fc23c07b8f9ee99a8891a92e20c759f62301c15aa1e8b26e
ikmS: 04a711d051fcca47e81f67f2a58cc3fa5317a654cd957652ef9b92c476b2e9b3
pkSm: 9a4fae3df449927a2bf610ab9bfd046982c80e3f7c71ee035db91aaa2d3bae52
skSm: a3bf5e01e525f0f71aebb956515458e19bc6b15030753c48a0fbbb9df5ca067b
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 988cf0d6b8aa4e4f2537270fafd1eb420d9aa0f1d2f45f46b00b83ce0ed8d433
shared_secret:
9c7b44f7a42ccc2c59337ea01668dfb2fe27752d63e3a9b0cca063f39bd427e1
key_schedule_context: 0351af0d3a80f50ff5d606ae45bf724c2f872698eacd389476
90bf75e1262a72a30f0d33c7dafc645fdc165ad9d110e77f68358179ad974a9a9b71dd05
5dec5eee
secret: 8dba7385a71625c6c398453eacd5c6989adfd92ba66478c9cf5c95171290e21e
key: 66cf248b93a0f0135360e2e45d41b6083011e49409f0910f8952b460cd7dd038
base_nonce: 8bc53640ac76c1b32e2556c0
exporter_secret:
74e1712d82b46d809bc8685ba01de89a311e40f607d8a32a1bc2d3d3a8e3b96a
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
46c4bf3cc8c3eee3aa352444a6677376c8677ed7fe2002fb3433d0286a8b0d05

exporter_context: 00
L: 32
exported_value:
f2410e92ba1944095537c53afddf84adbd5143daab8fe61fe4cdaefc39e4fa41

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
6c0a0faaa002079339ce7efedb2c4cbaa65f418c907e322611e279d0458a2301
~~~
