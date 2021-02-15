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
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/95396dcdaeec51da18ce099ea2e653e00f614738/test-vectors.json
    date: 2021

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
  labeled_ikm = concat("HPKE-07", suite_id, label, ikm)
  return Extract(salt, labeled_ikm)

def LabeledExpand(prk, label, info, L):
  labeled_info = concat(I2OSP(L, 2), "HPKE-07", suite_id,
                        label, info)
  return Expand(prk, labeled_info, L)
~~~

\[\[RFC editor: please change "HPKE-07" to "RFCXXXX", where XXXX is the final number, before publication.]]

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
of "HPKE-07" in bytes and equals 7, `size_suite_id` is the size of the
`suite_id` and equals 10, and `size_input_label` is the size
of the label used as parameter to `LabeledExtract()` or `LabeledExpand()`.

\[\[RFC editor: please change "HPKE-07" to "RFCXXXX", where XXXX is the final number, before publication.]]

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
an identifier different from "HPKE-07". Particular attention needs to
be paid if the KEM directly invokes functions that are used internally
in HPKE's `Extract()` or `Expand()`, such as `Hash()` and `HMAC()` in the case of HKDF.
It MUST be ensured that inputs to these invocations cannot collide with
inputs to the internal invocations of these functions inside Extract or
Expand. In HPKE's `KeySchedule()` this is avoided by using `Extract()` instead of
`Hash()` on the arbitrary-length inputs `info` and `psk_id`.

The string literal "HPKE-07" used in `LabeledExtract()` and `LabeledExpand()`
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
ikmE: 3b8ed55f38545e6ea459b6838280b61ff4f5df2a140823373380609fb6c68933
pkEm: e7d9aa41faa0481c005d1343b26939c0748a5f6bf1f81fbd1a4e924bf0719149
skEm: e539715b257cc9e81cc577233fec6316779be43505b026a957d27692c44a485c
ikmR: 29e5fcb544130784b7606e3160d736309d63e044c241d4461a9c9d2e9362f1db
pkRm: 46570dfa9f66e17c38e7a081c65cf42bc00e6fed969d326c692748ae866eac6f
skRm: ad5e716159a11fdb33527ce98fe39f24ae3449ffb6e93e8911f62c0e9781718a
enc: e7d9aa41faa0481c005d1343b26939c0748a5f6bf1f81fbd1a4e924bf0719149
shared_secret:
0c2abdf57191ee4118f124a746247a8be5c8252ffaf93015bf88e82e948bd551
key_schedule_context: 00725611c9d98c07c03f60095cd32d400d8347d45ed67097bb
ad50fc56da742d07cb6cffde367bb0565ba28bb02c90744a20f5ef37f30523526106f637
abb05449
secret: 8d13083972a08fffe81cbe5a103e5a09ead98855073da0fa5859592fdc9ecf28
key: c3b328a61b07876f2896f6f42361253e
base_nonce: ede5198c19b2591389fc7cea
exporter_secret:
d27ca8c6ce9d8998f3692613c29e5ae0b064234b874a52d65a014eeffed429b9
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ede5198c19b2591389fc7cea
ciphertext: f354b3145d4aa51bb6f41686d0b556475f655234a32fd061b30c34f89c21
31030870ac79b94c262794233cb4e8

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ede5198c19b2591389fc7ceb
ciphertext: 18fbcd5934f93ab5ee04d802178f17150e5d7f92b7899624d397c3271151
d2a819e55912e2ed27b12247cd6b8f

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ede5198c19b2591389fc7ce8
ciphertext: 76720ad8e52f30298677e387b1f3f87dd4d859383186a768d276b5f0e0b0
28348a8f4a4d051841a5d0c866aafc

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ede5198c19b2591389fc7cee
ciphertext: ba2b9d9a52e54289369a29f2d7dedd68012fa17c7c8afcbde97b7a1a4317
9444a65de222324a246f8dca459f13

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: ede5198c19b2591389fc7c15
ciphertext: 5010419ead07f77c6d33d7072705e09f8f246dd27b40f55fedc3958a495a
69cc826866c1afc96d960503d43073

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: ede5198c19b2591389fc7dea
ciphertext: 318599f66aed8878c8b414fabe504f89ab78b986fa20cf6394b18d1cf8b0
181c4c96275fed8a0246a24c4a5846
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
3f635126c12ebbbc45df49681e50b4c8492ce5e8a8d102877090f4840e0feb49

exporter_context: 00
L: 32
exported_value:
3ea056996a0dc9e045acc78db383777ec40b2ddb22a63e7132148b1acaa55b48

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
c20e37b9fc4605c5cffee5edb6754e82729290d1ee9e31b3cbbddf033343160a
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 9319c256d564db0185177c25ae7c9daf7493dff3f4c5222c7af8a35d34b619f7
pkEm: 21bde44b594f8ddfc0fc0deabb5df1e369bcbd95af6e121ce10c393b3c3b554a
skEm: 44420a8414ddad91223e87c605c2d73bf0a7837a2d4b6abdffa02fc711c327e4
ikmR: bff224d53aa4e043d2f0d5e808fd3b50bbe054b00015f26a440c2c942d31c9e3
pkRm: 7fe011337bda79458e6d7caeab9d00c40d385dd1f09af9279a0ec58df01fc949
skRm: 274a4ed7050569de19f327edb6590838858b803500fc733f85e08bbae8854e3c
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 21bde44b594f8ddfc0fc0deabb5df1e369bcbd95af6e121ce10c393b3c3b554a
shared_secret:
a82dd7a0ec89412846b02556b5b7e921f22d21c29c39bb9dbe985c1f7ae78231
key_schedule_context: 01e78d5cf6190d275863411ff5edd0dece5d39fa48e04eec1e
d9b71be34729d18ccb6cffde367bb0565ba28bb02c90744a20f5ef37f30523526106f637
abb05449
secret: 5acbeb369775f3cb582d4abfc777d606b8a8347178fd54389eff2e8f2475bc2e
key: 8bd91e5b91c25243b759df4e93bafe14
base_nonce: c04ed161a2cad4d635cd14c1
exporter_secret:
badf1b5662af9d05adb112aea76f13a35fe6c9bcbaa2c8944d02187accb02dcc
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c04ed161a2cad4d635cd14c1
ciphertext: 81b8e79825ca8e39cf5341c71e7952f69c964cdd4a8eb5835f3773a099e8
03b141c3cc5c77037a1aee64fbd9b7

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c04ed161a2cad4d635cd14c0
ciphertext: f02df5b95ecc1add39b6be5011544437031a557ad91686dc18515f0ce23c
0810f7ed4ecbb18bf46b4a4fb63c82

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c04ed161a2cad4d635cd14c3
ciphertext: 803018da30c22a52a4bc3c233a9eecb95ea2338c951750ef9997608d311f
be0306431159791e1092ea87459cb6

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c04ed161a2cad4d635cd14c5
ciphertext: f6593d1f82a857a0f3d1939b0de5b6630a478cdbcaa95cea32af3fcce774
8ff1ebc79f5c272be31a614f6c982a

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: c04ed161a2cad4d635cd143e
ciphertext: 5bc6488600745f5f581521ea1f0228056b3f46b0a984ee9331cb248887a9
7c7b6088d5c0d2b8ff6d5a26952878

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: c04ed161a2cad4d635cd15c1
ciphertext: 193e490cf4343791318c5259955fc9a0941bbc71b35e3dd6486b30bcede1
e46fb48e484f2cced2455f04b1a02f
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
ac4fab8b97b1b07807d2e0e7329fd81fc64663c32b61c578e2e709c8d43c58f3

exporter_context: 00
L: 32
exported_value:
4fdf77b70ee8b885936a771179dcdb62d194f278dd45530f1f472c6efd13feba

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
18adb180797cb58f6246288a6195a2b8e01facb5eb6ed0baf30a652285627ea3
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: fbdea51dc940c2cdf5fe671dacc6742675e66d0c1f933d22cac79110270b4072
pkEm: 167b8fa9e5183677d45f502593dfca2cedc0162e44368f39de03a0158c685112
skEm: ae00dc9c0cd4d03a28623419c03e416d4404767070b134cc5115f5c9af5d93ff
ikmR: 0d7bff4037bfa456c3545fe6f9068219d6fee1a56483a170ff0735e6bac86b2d
pkRm: e98a8846c45cac9b5420c709aff5dd82ea60f5208096d6c9cb635763e15a6838
skRm: e6394962f9769914fcb5a1e1d4f1192792058c810ba53dd1a5402fa7784b008b
ikmS: 45a6690472f0a47e17281462b1e012ec79e1e838ec950c00c013439b47ffa3d8
pkSm: 73b7fe64e3326c4ebd6acad4d52d89b9a5cd00f6f76211316fde9f7d4d02c951
skSm: f55932fafa429acef9fe650e5db936454df55c2b3671d8bb0551c28856ae78d1
enc: 167b8fa9e5183677d45f502593dfca2cedc0162e44368f39de03a0158c685112
shared_secret:
601b1e9f9d238091c78f01f92602a4b6739b3d57545e4c6c0e252122f36dad00
key_schedule_context: 02725611c9d98c07c03f60095cd32d400d8347d45ed67097bb
ad50fc56da742d07cb6cffde367bb0565ba28bb02c90744a20f5ef37f30523526106f637
abb05449
secret: e3bc5147b0732e4c4576c1861137db6675505a701aa1d536a36c749349cc11d3
key: fb0b29b5d915d998253aa345343a3f28
base_nonce: 6b8fddeda0cf0f2e710efdfe
exporter_secret:
7c6349699c571e768d7988e877a91b5307f9dfbb52de8d78b5cc6aa9083022f7
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 6b8fddeda0cf0f2e710efdfe
ciphertext: fcad483c96f316d46d8503714b549185190d7acd3eae9efcf3349777ef09
6b9e7bc3d8a65a27b976250a42a58f

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 6b8fddeda0cf0f2e710efdff
ciphertext: 6a8c15b22197b8078772f5ff4e65245606bb1149779bc367fde14b3abb5f
2d2cf08a4efaeed6d2da8dbeb23011

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 6b8fddeda0cf0f2e710efdfc
ciphertext: 0335a1005594c425a522f39274f1b385a30055a3d15a0e40a717c97415bb
b4bf266fb511e4880272fd9cc9c884

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 6b8fddeda0cf0f2e710efdfa
ciphertext: b26df3410ea4653628e1788917c4707e4e521373e8f810a6189af3d2d464
3a6898761ef3667aa7a8af15a494d6

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 6b8fddeda0cf0f2e710efd01
ciphertext: 014a0e8cee633c1525fde49c3d5bb8f6377b55c8ac5ded3bf6fbcb84b95f
97ecc338fe2984e910d48dfe79fa09

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 6b8fddeda0cf0f2e710efcfe
ciphertext: f8a34f5d93e0196684b9f05bc0f26f8b30f80abbcbb7a822aa45e95d8945
617bd4e058b8d449eab9db708d4a7c
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
7c0d3e8ac172ed77c98945f572fad2deb194714e6e8414e759ca102223a2fdfc

exporter_context: 00
L: 32
exported_value:
24d49f6c892945adf65320fc241737d3bb2bd398cee4820fc52dd228d5f4c762

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
ec4bb9f2a2be294d55e7b68ba1fb2925fa180537652a11dd63ae169e3acf5a57
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 94717743c08603d38df3fed7ea4058e9aa1ef90c58903b09eba027bd771e1fa4
pkEm: 7b0f6df1f9015e3af3373434d246d8053c54da5ca83a9b5cad27141f2d2a597b
skEm: a29e038a6f0633e0ea53a95200a636ae5d04dcf9d25eda1b30c7c8b1bc3a51ad
ikmR: 419bdd68259705f72f3c627693707545325f1281662ab331d295d2b98643b7be
pkRm: cddf59d3a054f31b7ee9bfb3a63e8184a21dd5838a65427d24d8336cc4806d14
skRm: b635b1cf133dcfb36858123e2ed3dfa810d276d6946659fe0dbd273e071c496c
ikmS: 0b3e3714f3fa314f77542e048a1345009f9a0ca5f23913674107cdbb2d62e905
pkSm: f0a4abc0c7bc83c9bd05e11be67fa3108e25dd298923cca127f8d5a131d06b3b
skSm: 59434fc6186de867d6aef7a7f68daaf86e0592381ae402cd5a3bcc17ddc4c686
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 7b0f6df1f9015e3af3373434d246d8053c54da5ca83a9b5cad27141f2d2a597b
shared_secret:
2141ff256b9d5b57f2aa8f1c4ffb86d9a3f53b8759ad6260df1ad43db22df39d
key_schedule_context: 03e78d5cf6190d275863411ff5edd0dece5d39fa48e04eec1e
d9b71be34729d18ccb6cffde367bb0565ba28bb02c90744a20f5ef37f30523526106f637
abb05449
secret: cf974d14014ae52f016dc0a779656e7fe6f0e8b71010cb7947b582faceeee733
key: fa4f6a8ab6f7a4cd1b2752ca932cb5cc
base_nonce: 27420254123bec2f87d265f9
exporter_secret:
960eef1fa7c981e924eb5e337403c2a7b7393d3134cbca2aefd869e4224b85f5
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 27420254123bec2f87d265f9
ciphertext: d5b68e3a6f1f9f50c684675af9944e99a89f91c7a892268da37b9f5fbba4
20f0955b0357b97c54f344f02e3968

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 27420254123bec2f87d265f8
ciphertext: ca4f6a6412c8d744ac3c4522648c1165e42b287cfa58625e967a27e748af
e44302aabb34966988fa0e25b9723b

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 27420254123bec2f87d265fb
ciphertext: 764ece873f6bd61bfec4a9662099f3c97760ed93ff67948be6aac4cbe37e
1a68389e4e65e59debe1bd05225b9c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 27420254123bec2f87d265fd
ciphertext: 1b12253186118c9c63adaa9746fed65a1d34878ed94af12d3033205780da
b50aaef0a55edd06a25ae39fda7d7e

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 27420254123bec2f87d26506
ciphertext: 6587e3e0afcea441bd33305ac327b1ac07ea4f64fa78e4bccdabe1099d79
4a120faa9510f3679e643f8e29175b

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 27420254123bec2f87d264f9
ciphertext: bf57adb61c0de8dce1298d2e9fee93510fbc4f4cdf4f5eef887b6bb831db
0d1f3513cb82c56534ab978251bd91
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
b571844a741cb10d16bb0a225c189381f38a21295481fc5f83276f8a2160f7a1

exporter_context: 00
L: 32
exported_value:
9fb412fc80917197be9e3378edf3c822fbe51a346af0a81247da7fba8502c081

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
004ae53a030665fc20af38998bc5060be81f831f8dd470fd7772d2935bedda95
~~~

## DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 87d4f4e53f9676b6161ef4e5a31fe6e5ca9466bd4c04833795a0c226891e37d3
pkEm: 88edf95a04ab0bc3f3c31b2668c8efe3746b6632b5dd2e75e6b4e9664ced1c12
skEm: ff29ed7dfc1c4ecb4a9c7b11f59aef189d431e79e8026c85dc9e20ba5587c51d
ikmR: e54ac4d56e2bddc3f27aa2643fdbb7e9e9959a5eee15e3742f37a6129da1fb76
pkRm: c4e460cb28e2ab8d6d0b308fc9a04140ef9f1394111c794215dbd9431e859d6a
skRm: 3afc703b6593edc62667fc41c12a751094d8b479a2b186a58636f1d8a42caecb
enc: 88edf95a04ab0bc3f3c31b2668c8efe3746b6632b5dd2e75e6b4e9664ced1c12
shared_secret:
f50c6b9919f8bca36aee551705c53a5dc2b5cd19fb9194498d622df74a232af0
key_schedule_context: 00431df6cd95e11ff49d7013563baf7f11588c75a6611ee2a4
404a49306ae4cfc5b69c5718a60cc5876c358d3f7fc31ddb598503f67be58ea1e798c0bb
19eb9796
secret: ed73e63d2d966ef2fac3fdc873e0baecba1e61b750ec4b9402f1f2bae4da6770
key: 880923ffd11090fc65a573e3d069d1a8cee86afaee4b7ced2cd9b093c09611a7
base_nonce: f621dc5bb2d0254c3eab2662
exporter_secret:
f891a23b0131c09578795d7004d985f1b19276a7a51a0663219bc31a53cfb2e1
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: f621dc5bb2d0254c3eab2662
ciphertext: ec454f2fbe381c7e76c4fb0f5c8fb1c5a3218e9689800cfb659f884c5b76
fee897d93e8ec1521ac1f6923871d3

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: f621dc5bb2d0254c3eab2663
ciphertext: eef0642046b4a737d8f058936f26cade135676d401f6a49f2ae90657dfdd
bbe6059bf4b9f0d38efe09f498cbd3

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: f621dc5bb2d0254c3eab2660
ciphertext: 16b70a33b7558a722be5a3c31d60eb7b3507c50dd0fc87ca67294dbdb126
4cfb535cef4e7e0c51f7490605f05e

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: f621dc5bb2d0254c3eab2666
ciphertext: 01dc8512376a627bed6c1349ab6c29983a5b3d01e2999cc65e0b7dd4c16c
d753834f412bf02af2c1940d249c3e

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: f621dc5bb2d0254c3eab269d
ciphertext: cf5944fe2387aa1441696a7ac2fe10369a5a013452d82369b77010cf6276
dc5ed9e42dbb889ee8d19f1ea5b287

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: f621dc5bb2d0254c3eab2762
ciphertext: 10e25dd3a1d63602020819e58dadf76a56b36a809d24ed9241a35e11d016
766c5f4a38532f55975997ce44399c
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
71da8f5d27cac0c9c693aba852c6bc468581028a9a9cc61278d1fdbfb7e36f0d

exporter_context: 00
L: 32
exported_value:
9f0dabc23772950ffe908e3c1838bba2ecbd4d2ff9601f729095f7d10451652d

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
51de9fb22c3c9721ddac64470a37c9800d3b14452b9f3546a697100509653028
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 2712b2c0b0859ec640f020dd0c44012a87984320b2015276a50b07bbb082b5f9
pkEm: c66d85bd4a024ca62c8871777ee56fc0fc6f059e9fb6a066fc6e97f11cbc2856
skEm: 4018e14c7e945b097a7d003a95a89d7738bedb47e98c71ab571a621527feba32
ikmR: d2c32d6ad4296054c438cd124da2b05619479ecdeed8c9891a772df50c6039e4
pkRm: 13e1602022e14fbc3afea130fef46757c87b9dd5c41061582654c54c1e3f2901
skRm: e598cb0a9bd89e6f2f7ae3d498a803d21b9f00155e8835cc1517469c4ea896cd
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: c66d85bd4a024ca62c8871777ee56fc0fc6f059e9fb6a066fc6e97f11cbc2856
shared_secret:
826d51c2066661612d1a6e71525b1fb3bd649b2ba82a5b61a901f25dad7430c5
key_schedule_context: 016870c4c76ca38ae43efbec0f2377d109499d7ce73f4a9e1e
c37f21d3d063b97cb69c5718a60cc5876c358d3f7fc31ddb598503f67be58ea1e798c0bb
19eb9796
secret: 22a17d98f976bbdfcf24a891b655adf4b45a0c95dbdf56eb079b33cf6064174d
key: a2ff2631111bd02de97533e5d655b9d9460416cf1432f2cf1aafd037dd350664
base_nonce: f8dfb8c86ade72b79bf3fc47
exporter_secret:
090ada39eb5f228d454b8c107ec246c765bf45a0f19b74321420b51366080ae4
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: f8dfb8c86ade72b79bf3fc47
ciphertext: 0d3bdcb76e631891863826a9745241a88a79c7873ba6de727c02bd84ebdf
c3f429a5b20d4e92b95eb267e94374

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: f8dfb8c86ade72b79bf3fc46
ciphertext: 2c4f8d7316aee3c2da785f044964954cfb777cd33aec995d81d51a9ca8df
74398c4322d1c64d9084c090082d4a

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: f8dfb8c86ade72b79bf3fc45
ciphertext: 4a00614f65b6cf2211d89a24e6c23c2ecb67efda6a044e00462def2e2199
1d27d343a4f343c5b5a52e2b5607e3

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: f8dfb8c86ade72b79bf3fc43
ciphertext: 068bf84bbbde640fb1710c0041a6c0ccabbc4e74b3788182b3a1d298182e
24e3968978e4f5590cca8dca635160

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: f8dfb8c86ade72b79bf3fcb8
ciphertext: 9b0b2d4b50e23f2a6cdb1e334ea7f386e3abd4795d2b7f38d822d06591f3
1644b6ec0aa17f3c909aa07cd1e879

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: f8dfb8c86ade72b79bf3fd47
ciphertext: f10d1cfaa8cf75f6c76d8b1b475c45d6fe03fbac791ee966284d8108953b
678fda8ebe8aad76ca1ab6b29690b0
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
db77211c501908b49cb320bac3f5628589c434c68b744c1d6d6b73628128be7a

exporter_context: 00
L: 32
exported_value:
80efc21962fb8b00b168d10fc1c7e50815bd763521b4ad9f3f98547fe1104122

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
b9da2c091f23e76df6d7d688c4f9cda487c0889eaecaabbfa16c0edf0a1cf9d4
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 69d08e1e595968d2053f47c798dac15bc4b0f735c26ecf062b9d3cb831d2f182
pkEm: 9e04b5ee73887b9837689b9ce6892e770efe648d5784a512dd7c70664f74b920
skEm: 3a1a1090bd044c1ce3e3e63b0d8fc777746b585fcb33ed84a1850a09d182060f
ikmR: a18c2d131419c4f6ac021213ad7f7a2ed5c6205da60f7bcc945717d2f214f1bb
pkRm: f04bd633f71312fee806cd3268e3ca983053999573f3e503178b280ae6432501
skRm: 6bef59d28e988536d7feb48f1971f805448b043dad9188f71f9bc01a1a71f8f4
ikmS: 7c7e7a518a6f2847035be6b90bf85c19f8d8082fd9fe96fb8355c924cca241da
pkSm: ad56b8f31060d6b93e25fad4a6c7ad56231412373509ea8c9777e7a48cf8880f
skSm: 6ae5e996c3caf2857e2947a4949191f6dcfc7533a94eaedb9576ab2ee4aecc45
enc: 9e04b5ee73887b9837689b9ce6892e770efe648d5784a512dd7c70664f74b920
shared_secret:
31048a2bfa065810da8bdb4295e12d9b2ee7255fec6e7c0df3692217c04e36f6
key_schedule_context: 02431df6cd95e11ff49d7013563baf7f11588c75a6611ee2a4
404a49306ae4cfc5b69c5718a60cc5876c358d3f7fc31ddb598503f67be58ea1e798c0bb
19eb9796
secret: 8ce71724bb3091a75a42f3b0cddc6c56ce22f3e988dd0a478298c644eb08ab21
key: 6c336a7981b95e762cef3d8159482a8886a7939fb04e836e150d47996a7e0cce
base_nonce: 7acdcb8c5ee94f3a7dd645de
exporter_secret:
93919dc183d676a27243915ad028b00ff642a579fbba74da6ce3e29c14cc87bc
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 7acdcb8c5ee94f3a7dd645de
ciphertext: 0c6bdd5c5838e8c25cabd49c5d552416f7bdddf3122ec04a44c53fd02e71
cb59ecdd427e33000622337604aed9

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 7acdcb8c5ee94f3a7dd645df
ciphertext: 424eb67c86c13e05ea76b888193bc7171dba0c74b52d28b0812005a9758a
9899609e623e262e702cd703f726c9

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 7acdcb8c5ee94f3a7dd645dc
ciphertext: e6e0f158ab7ad362134268adab58bf45d789a9e1bacafc1df759b2227584
d4113afd98398e1f54d98919148719

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 7acdcb8c5ee94f3a7dd645da
ciphertext: 6d8bdcb6d81d20a644d2ed55bcb70996e8c3da93604d5aa790c6d244d4dd
1057baeb91af2471a8097b4b61324f

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 7acdcb8c5ee94f3a7dd64521
ciphertext: 3d2fe38067e961e22c78152e2efaa7ef2c5569e54b975ccadecabbd42cfa
4e4b8ab3535055d2cca0e1ead808ab

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 7acdcb8c5ee94f3a7dd644de
ciphertext: f9ef62eed95ae76bd6dcbc0650ab5507640c1e7dc9cc9790a34b402d2165
a316240d9de7fee30df57f9373b6fe
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
926e6287ed43414c63805d55d6a54d01aaa06becc4086c280a10e1695b07ab75

exporter_context: 00
L: 32
exported_value:
6d7411443b3d7b4158205ca2776ba293cded4644341f553a9d796bc6dbf0e894

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
91b5f5dcb4384186442e90e68f261bec989e379ef63ab3818bd758237401c8c8
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: b077c65b0683d43ef098615af7f127a78cbc249fe19504d211ae9305226137b3
pkEm: 8aa12a38874f8fe3c5fd4a818a34d58a2154fab43105315b25ef9168b6bde06a
skEm: 5b29c9d159351b44666d3836952458a49664f2b0af427ec6dc4288a35642e9a8
ikmR: 333fcb874363ea60ccc0b8733b560cecf1269b30b4b83fe9ce78d7209305788c
pkRm: af703ff3a5e933ba9d022484096547531db042e3539e3d34202206a1969ed96c
skRm: 371691937971d16165f1de38f961eaa7a514c66ff4ce5c56a6d6e1d50882763b
ikmS: 85610bb5e3ae71e3c8fc0bb7e2ec41e258084b5177fc803f5097b1dabddf216e
pkSm: 4548bb795392bade5d87ebacf21db6711b3c3780bf16f0279cff0c79288f334d
skSm: 09c59cafb2e537dde120a28f693d1614b3f3f6093ba5b28387c4889cc35d6622
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 8aa12a38874f8fe3c5fd4a818a34d58a2154fab43105315b25ef9168b6bde06a
shared_secret:
26f5a9edfa782d12570d1cce18c85555aed650486cc1dba23a6043cc5e50c523
key_schedule_context: 036870c4c76ca38ae43efbec0f2377d109499d7ce73f4a9e1e
c37f21d3d063b97cb69c5718a60cc5876c358d3f7fc31ddb598503f67be58ea1e798c0bb
19eb9796
secret: 7a82821cab3244f123d0ccc7871284a33fa45161f8ad79e0eb7e2a9e095ac2a2
key: 6547d337a8bf2f69e581febdaeb103cb093d83d45522ea84d13dcd56d8810718
base_nonce: ad4d5dcaf521aff128c108c3
exporter_secret:
1e617a5118cd9923dc55e3e59aa7fbb3410d4d5c1d355bbdb7e2cfe3aef7668f
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: ad4d5dcaf521aff128c108c3
ciphertext: 2ec2ea5a23201a60c5e1909c16afd96eddc01d63e24bafa563fe1751e52d
ca300f6d6c78a0a5c2ed30d4e30a61

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: ad4d5dcaf521aff128c108c2
ciphertext: 38b0575058d40f5d6e52ab67fe4e96ceda0061e20b023a10b2dd5ad8bb5b
c60a5cf33b7ba3c6fe0030ceade53c

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: ad4d5dcaf521aff128c108c1
ciphertext: 39be9b6e52cdecdad6f2572e898171fa5e2d1b0a52eaa5b1aa679c71a66e
b8a4e8bd34a4717929ceb2116457c8

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: ad4d5dcaf521aff128c108c7
ciphertext: 74d035e550feed98520b83c8515fda63e7bc324ca367661d6429b2e339f8
b1ed67add9dbc21b648e99c0c6ee74

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: ad4d5dcaf521aff128c1083c
ciphertext: 619d2a34997b7eb42ba0042c6bee7027b2e76dbd6e1668a581f2f9fd49ca
b769b68139f65761b3ef92d53f4506

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: ad4d5dcaf521aff128c109c3
ciphertext: 0b9e4a729d1b92940ca1d866aa28f053858b584d1907f49cb6aa01022182
921a57e1ef986138eda8bdb3567bb0
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
26d18b3e898bc24ffe1c87b051c121e4b4f3be1be4a39bb794a6d61b946f7b91

exporter_context: 00
L: 32
exported_value:
dff97643358d61b385a8adda1561214808185503ffd31490b83620803a5f0c4c

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
9c0917b3d2f7b10267d630f3a71b2caf9a2a451102044a76f0bfce9e5ed75c85
~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 80fdbddefe3f492781744066e5dc6de5d45fe13733894417a5db66c755f8f7f1
pkEm: 04987cd3d8ca7b11f4c05688b9ccc569210ee5ed3ec3629e1615ba2b6f4834ced3
5da40bdcc786e1c523e4dab1794d540cae4a565aceef24685e64d646a067b385
skEm: c13f314da45f296215553cb08736cc542aeb13f211c9632f232a82ec843a78cc
ikmR: e8c888795334a26f9d31d2aad14827a8d585c04122daff292095497a00be953e
pkRm: 04e9d622b3112fe22a0f3c9e1fa6d020d61f3efb58652973a8f5c4656dcc2f63ee
fbf14e6f9d7f7b7772a56ddebc13ad0b1a0a9f0483b2a1a8d6cae615d9be3ea9
skRm: 6f14a20f859eb121acc2dd77b8718b2da5fa6a38674d93cfc74e57cd5d4ae51f
enc: 04987cd3d8ca7b11f4c05688b9ccc569210ee5ed3ec3629e1615ba2b6f4834ced35
da40bdcc786e1c523e4dab1794d540cae4a565aceef24685e64d646a067b385
shared_secret:
44a7bc0b3dad29cf35610d43e8b6a3bde6427ef3d10c1183b815c85733f7ffbe
key_schedule_context: 00b88d4e6d91759e65e87c470e8b9141113e9ad5f0c8ceefc1
e088c82e6980500798e486f9c9c09c9b5c753ac72d6005de254c607d1b534ed11d493ae1
c1d9ac85
secret: f1072d9c35101c27ee0820aac493544b355910e2b05361ddbf37cc184f03d843
key: d481191a63ab00c15e5944bf8f202673
base_nonce: d4f41cfeff8942fc569941f0
exporter_secret:
1df76f92322234f75234ede58d20153265b95244be00a44a218ee45bb272180f
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: d4f41cfeff8942fc569941f0
ciphertext: d5b8fcd4d6ef4e70652130d0a976b699b94880714f9392cf818031e3a51d
c938987504d6c12e91f4936ea039a2

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: d4f41cfeff8942fc569941f1
ciphertext: 8d9e43d004e28895ee45637762922310e6ce97e1d57b6db9d7e3cc43f46c
838159ad66ebff88e038ff56653161

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: d4f41cfeff8942fc569941f2
ciphertext: ae633e72bfe94cdf6ebcafcaa6e1741255846e4af714a56503dcc9da0c0c
c066265750494130f4b81b571adda9

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: d4f41cfeff8942fc569941f4
ciphertext: 3aa4fafa2b1bbfabdc66e5a34d362ea1bc933a1335d1075e0b6cef6c4c50
994a40b6016101cb5b09510bd4fd3f

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: d4f41cfeff8942fc5699410f
ciphertext: 9766208db2eb7439bd7e8de13b230cfe18e7f51c0b35e51ee86646d54f41
31d9ccf9cc346ad8a1eee7c33e2000

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: d4f41cfeff8942fc569940f0
ciphertext: 9fdc618980d7683137740e871d786a6ddeb444ea00cac7568bba7c23fc5a
b5029faa5947b6329a03bfca53344a
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
2a5155420c36ba4d3fed081223fab445d57d0a33d85115dd0e9c44b021aa8de8

exporter_context: 00
L: 32
exported_value:
e81e4a73608e3aeadba7409e3e161656308cf5869c6abbd37f8a0cd6b5d66a47

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
5a9bb18c06b8ae41361f517c4a51dc2321b62bcacae5a32c3f28bd03d2e9386d
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 6f84a21d43a6c1924b370c73130b4e0bedcfccca2a327e343fb5eb36455fb878
pkEm: 04c1a5348ee62a6866c4bb199653e62dc3f283b03f819d27254e28343e429c831e
5b809752fe9a56c77aef550f3d171f45a397f9f372155e994ea925bd432108ed
skEm: 5a2e8a5cdb4a39135b09e09c01c4e62ca108ff8ac532f54625a6b3b256a893d3
ikmR: 8f9b609078d0b7d6efbf5dc56118e1e9097423338ae995f30012ffb0cca1ed3c
pkRm: 04ddbd6a55bed8047e640e89696945faa660b71699a983e29e5796f462f30eeac0
43f2455508eb6b4866a08a380e4482283da2374d62bf2ec70090a16b88c4d739
skRm: bbf45b62d58f4294f3f1b72465dc54650f8d1b304a205625493aaad85b5e744c
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04c1a5348ee62a6866c4bb199653e62dc3f283b03f819d27254e28343e429c831e5
b809752fe9a56c77aef550f3d171f45a397f9f372155e994ea925bd432108ed
shared_secret:
889d1e726749d77e05ed4bfef55d98ab265d2f429a775e2ec577d1225f8ea593
key_schedule_context: 01b873cdf2dff4c1434988053b7a775e980dd2039ea24f950b
26b056ccedcb933198e486f9c9c09c9b5c753ac72d6005de254c607d1b534ed11d493ae1
c1d9ac85
secret: 05ce45ea322deefe9b6579e906a9d9d9beead40fe5da3f3bad215947f2591a8c
key: 8386f83fd3f47f91f04b6efe1ea99a44
base_nonce: 000f4bc87c80a3d75e2a0787
exporter_secret:
c4c9881d1bd4581fcded1335bfcfb9c006a809f5a1b8292ba1632fcb54b85106
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 000f4bc87c80a3d75e2a0787
ciphertext: d721f0c795458488ecb441019872663b4d4a5df84c2af21887b6e02b3e8d
84c8a2269ce7f507848ff5760d6d11

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 000f4bc87c80a3d75e2a0786
ciphertext: 8ce87b65a59c709d83b471a89c8ac9a9338b6ab954e5531d4c5bd1f81fea
36ca580b12a47e09d683ce83530eb3

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 000f4bc87c80a3d75e2a0785
ciphertext: 65b29e0ca928cfca89e495e161b67c0fc38b908e6c963494ace993670f02
a0812ddd5da87f08b08a833291fd3f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 000f4bc87c80a3d75e2a0783
ciphertext: 1e4bb5af7716ccac6de0d7bd1ba980d16a8b3ada2b5fd87c4c5d156f5cc8
67569121a1f05b1a69b4f31fc9d924

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 000f4bc87c80a3d75e2a0778
ciphertext: 2d4dc7b24feb474121a43cbbcd3051cf9fbc19d15d61b224a5f1edf026f2
b56dd47b8b33248db32d09a7da7ee3

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 000f4bc87c80a3d75e2a0687
ciphertext: 07c0ad9b2a402e5dcb4d43e31be7ec2b5f25189dfd3928920be4db167a3d
c49fb2354415d9f765cf1f6437ef65
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
4d44d7ecc1b45f3b542d88bd6f8faf9ab3a1457a90c4f30907cafa42f09d8d2f

exporter_context: 00
L: 32
exported_value:
7a9b31d89929261c272e7d6925f6c6fd1e28a3719d4308017eecebeed0024d52

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
c1426336ac07eec24d074586413ca76f57cbf538bf98cd5246d9f92bedbedfd8
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: b6abd0030f59191c0ad40731f2252939a932071d70e705fc93a8fe132c0f8dda
pkEm: 041f751bf2c74740e0674c08f7383df772c0aa1f6b1685418a400606081852a1d8
ca423985cdb5c082f4bca96ecedc9838dbb66085d54408256012eec7853316a7
skEm: d25dbd2fa7a6e511d9ea1c8efe63afa77a5c41ddf1932ca7e94226c18093145b
ikmR: 2121fd02805a11c355fa29a68c1434aa6944c111f84e8fb12041e279e6a1e6d2
pkRm: 046134a8c1567c20dc266a9546b7a2808cc34714389b29bc049a5fbbfe8d07dbe1
81ddfdf5cbf56106e009f5372d3cab05bf1d359b3a9edcb4a620f06f45be1c4a
skRm: 78d4f870a8ef145b9d2f95516b18da0d3022377380b77162e24dc581973afbab
ikmS: 1fa15119ce0c1ff6cc786921fb72b5d0ee29f63d04876f82017c642542c8b3df
pkSm: 04f32da29172eed92b23ef5efa8fa6152de89b85491ad7b9b14b5427d502829853
d41220c498c3c662eeeb122e5093e167d6096fd8caa2c6bd1edc3417787b6eeb
skSm: f250dcd843fcaa434e54aebb180a8e5486ed290663e9757950a8c8d39876f6e8
enc: 041f751bf2c74740e0674c08f7383df772c0aa1f6b1685418a400606081852a1d8c
a423985cdb5c082f4bca96ecedc9838dbb66085d54408256012eec7853316a7
shared_secret:
5dfc317b57eda82d46127e3915c3824b7945db2d402c55b5b3d7d6134587246f
key_schedule_context: 02b88d4e6d91759e65e87c470e8b9141113e9ad5f0c8ceefc1
e088c82e6980500798e486f9c9c09c9b5c753ac72d6005de254c607d1b534ed11d493ae1
c1d9ac85
secret: caba5d537619aff7a3e6a80a94e506fe5b7b7e70170698ea6f8570d679415a23
key: 7720594cc02c7f6276b2cadd9fb21ddb
base_nonce: df521f26f03686bfe5016753
exporter_secret:
241ba20325013c2860e81ac524813619f6da9be1a6e55245ccf742886421cb18
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: df521f26f03686bfe5016753
ciphertext: 969d911e3157029312daad37d901762561c5aaf67cbb1533a6872748c681
430cf036dd916d9279dc3491b42a5c

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: df521f26f03686bfe5016752
ciphertext: b472e2765da52b59db7218ec5cd9a9656b0f99fdbdeb8d848ac88a14430c
5b9a4e9dd1f040422a6bea60f1d733

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: df521f26f03686bfe5016751
ciphertext: 920680a88f391a9885e898d6103efd94c644af167eb5fdd3f5a05c79f1b9
e8d739807b8bbabf9a7d2adebf0008

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: df521f26f03686bfe5016757
ciphertext: 9f17dce45607c765cbf4e6a721be9fa5c8f70a9e7a73980d5f0fb7669960
2063162dc216ebe38dac514a1b0386

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: df521f26f03686bfe50167ac
ciphertext: 5148ed93bd976e31e55eefaa8cb6eeb35332a26beb1a3c0dceb19b6ef44a
51c049b3100cee30b5756c07028760

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: df521f26f03686bfe5016653
ciphertext: c45ac4a6f75211191d3b4bf5e9e80832be9e546ed94432f962cf3f299140
a12e36df7b6afce4140aa2c8d18ac2
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
73f6f2a34bd53dd6275b556ae5d9daafc7b3a2cab1a11cee854a3d52d9b44fa0

exporter_context: 00
L: 32
exported_value:
9429a7c29326a76996385f123df3bb00e2eb616e6afba0868b4d0455ca0654c3

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
9681d6a4c7e0406d7df7b0195b28a296109dfc12434372e16e9dd2c208aeaa99
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 869cbc0bca8c56610d99b113101884eb9f465692e67efcfeeb57f177411fd4fb
pkEm: 04c5cb56b75f631060e9d1281f2885da58b176ca7105f2d28c3f61a7f2717f205f
47a4b44953847b977bc455cd6251635a8b7898f5f66969236c4122dc396eb99f
skEm: b70c5e4025f525602c912b1ceed0a87424e0c41547afc43d014d420a8b3498e7
ikmR: 50c2ba8cfd899d9835246337517e37122345cb61837e0d36409657e74a19f304
pkRm: 047176000ad052d41795c712125558ff6b0e5c802fe5974305b8eff501befbc1eb
30788599a497a671679b5b10779c7cd4120dbf01e96f625a80ca0eadb317111b
skRm: c3ace5184b62e0f42a7d4b09f5e782d763ddc34f165aeba5a54e46a86cd2c2d6
ikmS: fe93094796ec444427e2379fc9849388443efefec653ae31df273bfb9d3b6b2f
pkSm: 04a486001eb537013bba008f57810d71506161c007712ebf906ea27c88f83cb5d7
8e9bd301fc58fbeb36ab4b4fc687d041014123894dc401fac4b0fd38c71c08f9
skSm: f947b19ac51a7056d28611d9543a80ee002df9a83e0fc62b11133607afac2b22
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04c5cb56b75f631060e9d1281f2885da58b176ca7105f2d28c3f61a7f2717f205f4
7a4b44953847b977bc455cd6251635a8b7898f5f66969236c4122dc396eb99f
shared_secret:
335c0a6c700daa8c2c8812813d4a2659261c33502cb9de7c78e041b32a73c934
key_schedule_context: 03b873cdf2dff4c1434988053b7a775e980dd2039ea24f950b
26b056ccedcb933198e486f9c9c09c9b5c753ac72d6005de254c607d1b534ed11d493ae1
c1d9ac85
secret: 76f6f36fc63231766b373ec23a03382652f577fe5f24cbd3392c75daad45cb4f
key: 6bd8a69688380d51771f436a1561382e
base_nonce: c2d268732bb6fd01b952810d
exporter_secret:
f23fe7dcc0df31928fcce756b82fb2d909f1e246d93d1922ae6c329fa3260cd0
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c2d268732bb6fd01b952810d
ciphertext: 32fbfa12b2ee6c45c4914c145024109f0f198df415a70bc8b893a820edd5
5891d3c7381fde11f99a0c39e11929

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c2d268732bb6fd01b952810c
ciphertext: 301fe5a5111dcc5e931f82a0baa463f1355999fe860db1b6cb80d7000dd3
1dfd9315ff959fe6228edcf7ca5371

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c2d268732bb6fd01b952810f
ciphertext: d715dcd7844d579937fdd2e9425313c69eae5589aad1ed470e115fd55053
8bc68850d4d24b392433a3cf47f1b1

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c2d268732bb6fd01b9528109
ciphertext: 27436b173926cbbe25dc1f591af6f551f8c6bffb14257b022cb8526f0bbb
e5986dbb5244ad568bff8e3f43f582

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: c2d268732bb6fd01b95281f2
ciphertext: 3f6e0f1a4090feae0f8e2d172d3d3e1becd03ad6b68cb05d84e0638d7368
9cbae2793589978c33f559c410651e

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: c2d268732bb6fd01b952800d
ciphertext: 8d8fc22e84a4192309ec320a107257c67040b91297e94b3345308ebfa036
896e139c78d82b0d8ff2328408620c
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
c6fbfece06bc23430f0bceae2d76860ce07c74982e91177b4d63ea118cb13f20

exporter_context: 00
L: 32
exported_value:
dd731e2ee1a6a2dfa6db5e30580fa794d35920f8334b5d1dbc3b4baadcb326f8

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
af27c19e5bf753edeadce501537a7c15b97d2f149e0f8a83fae4ccd634805ea5
~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA512, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 28963e0f3e61f79bf7399d84e45bdc0ee851be596e45de1e71327c5dfefba5a6
pkEm: 041806a5976c8d35afa7b33cecdc36db634cd13f43ef210673049e15667b6531e4
1301b58a825e2866266d8be874f863d7d9260a528b1700121ce977c1b5855d2b
skEm: 03bcd6eecbe7c2983cb094d258aad6352e66524c0bdc3ae55bfc5bc3dec5372e
ikmR: 1eb47bf4bea536ef902ca2825476c8b3fbdc4d97f50d684a8bb803819c03d068
pkRm: 040e221ce4fca009dede28ea7ced95c78631eb7d7c20d38d186ef215b10c0b79e6
61b020adb46be403529f569e5935396545db9374144af9bda3307a99c2195160
skRm: 14b36ce453a1aeeeefbfe41232e2391220c7dc8c9f65480e44153a60df4a716e
enc: 041806a5976c8d35afa7b33cecdc36db634cd13f43ef210673049e15667b6531e41
301b58a825e2866266d8be874f863d7d9260a528b1700121ce977c1b5855d2b
shared_secret:
624cbd2569ae306f1847e9ec6b8b210b5fbd7f802062b8780fb0ff7b5d780871
key_schedule_context: 005b8a3617af7789ee716e7911c7e77f84cdc4cc46e60fb7e1
9e4059f9aeadc00585e26874d1ddde76e551a7679cd47168c466f6e1f705cc9374c19277
8a34fcd5ca221d77e229a9d11b654de7942d685069c633b2362ce3b3d8ea4891c9a2a87a
4eb7cdb289ba5e2ecbf8cd2c8498bb4a383dc021454d70d46fcbbad1252ef4f9
secret: c59c5d18bcb0b16c2e8e3bec8af64d58cc3daa70be0684cf171a899248095144
dcddd75139498b16b4766cc7afb8b253fffe7ee1cc0d7c9e9fc19a6670d743eb
key: 54cfccef9fbca8aca71bb5af238735f6
base_nonce: c84660f02d09b919fb2b651c
exporter_secret: 8913aada22307c01b90dc9f27d5864170e77edfd1cf902384f828a3
fea101e4eef3fce6dc93008c2e9b5eb05b9536afd9afb0be7671172d70b38bcd15e560f4
c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c84660f02d09b919fb2b651c
ciphertext: d4d41aa4d44929cb4b1a2f411113d03f4b171b89bde51fbb377d23bc6d8c
aa887a2f3e54d8a432702d70fbf577

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c84660f02d09b919fb2b651d
ciphertext: c4ec97cff2b3ae3a7bd5b591904cbe3ae1c79f5559434947d4c4fc91b28b
60d91cbcb84df145e9fbc3892716c9

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c84660f02d09b919fb2b651e
ciphertext: 779d831d10ad22259a6f2bb2e3e9d9154ad88ff37f579909495b8f8a439d
c36fbeca27e9a5eb07e90813f75983

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c84660f02d09b919fb2b6518
ciphertext: 161fe60d372ede34dd6bd53e648603fc110bec86eb6ad1e6e569a0652c3f
14978d5b05782f60f159cd2129db0e

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: c84660f02d09b919fb2b65e3
ciphertext: 27b48cd83a76664904af95866825b71e8eb97bc0e5cad40f47daeb80cb8f
f75bcd210337062bce48bfd92d4035

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: c84660f02d09b919fb2b641c
ciphertext: 1e77052fc876909145f1fd9dd294a4b6e5bd2e1bc774c103110454857b4e
c5a41e202ff0248880b1dbb25781ba
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
88e9241f873dae2bc48f4ae7d1e0d416d210b0f5cb112fea55bee2b90917072b

exporter_context: 00
L: 32
exported_value:
f0877af5d68573d719322818be0fecdb0ffb7ec587cfd5a13b49d161a2fc0c84

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
7fbf28c76410229fb24658f53cb7679f78a98b28bbd2106eb790d2fac4bb666d
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 2411dfc68d7dec030ce731c1d01a6190965eb6e916cb917d27f63d74b3cc1c17
pkEm: 04b1de1db5c453f7d41f7ebc5989c4fecd7db41463337b7dc63219bd2fe3b53652
60698e7d5cb4d33e52a5d69564593401c52f5f441fe93a962c3ead4296773d75
skEm: e8ace3fe729f5ae532689ec81c38f3ed2bac17127a5790edc4af402e8846f35a
ikmR: 4b4b5d3789d3686e9884b769919d9a0f16ff7f7ffac4bcc405cb7cab70789c04
pkRm: 0440804eb69276ff41e199e7f1487162174e1ce5474a57ff9c279d6d580018f295
dad6b781e5a615f19541a0f0818b3a0150cd01e4a95b6a8c01b8dc9acd8e30e6
skRm: 3dfaeb9c3a37392908e01f19c93ca00b6cad85d06435477aa289fda24d0afe7d
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04b1de1db5c453f7d41f7ebc5989c4fecd7db41463337b7dc63219bd2fe3b536526
0698e7d5cb4d33e52a5d69564593401c52f5f441fe93a962c3ead4296773d75
shared_secret:
44ef98ce6e099590249915175b1f5004e072b34f427f913a7bae70b9524582e7
key_schedule_context: 01713f73042575cebfd132f0cc4338523f8eae95c80a749f7c
f3eb9436ff1c612ca62c37df27ca46d2cc162445a92c5f5fdc57bcde129ca7b1f284b0c1
2297c037ca221d77e229a9d11b654de7942d685069c633b2362ce3b3d8ea4891c9a2a87a
4eb7cdb289ba5e2ecbf8cd2c8498bb4a383dc021454d70d46fcbbad1252ef4f9
secret: 4e6563e6320dfe44581b775fdd63fb79c3532fa622f8e95030972df625111cf0
c47f99b41ea3cb0a4b2d58b0c35cb5bb3295b172b7506e4cbdf32e3a8373c9bb
key: 319a4b7e3cd960c7b0616c0ab2ea39cf
base_nonce: c21db1d1c97ddfc8d11fbbd3
exporter_secret: 123a854cfd2e2a0da0ef02fd74585f9b8376d1cc375eb1f8736ce85
6bdb75b620a516bf535216877e789d154418386a9eea57c606b851649043b3cdcbbf674a
7
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c21db1d1c97ddfc8d11fbbd3
ciphertext: 1966e971ce4a99b142b78acd758b889341659b789c8b122ed7d8a1d2f8e7
5fda680ddd03f239a4dec63d9af446

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c21db1d1c97ddfc8d11fbbd2
ciphertext: b83ee0d0ffb3b5c289af8893b8df957220782ff359dec5e129aafc1057b7
8493ba9650efe83e950fba9c618e15

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c21db1d1c97ddfc8d11fbbd1
ciphertext: 33b7d6ab925bc7c12bf91b89d82d565701e8cac6383c0238566e221fd4d0
6d8eb22d802ba3e8d9eccee81fd279

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c21db1d1c97ddfc8d11fbbd7
ciphertext: 20a6d22e157d626c373cbe1205287be76c4f85cad53cee8b59f949b6e601
dda0511b72b3fcf39c8eb5cc47bf20

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: c21db1d1c97ddfc8d11fbb2c
ciphertext: 6b20c35619cc3f0d703ed9239a8cde73c9540134e8188fa42a2746121085
bdbd91ef53c4c525919d533a728378

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: c21db1d1c97ddfc8d11fbad3
ciphertext: fb74cb294bb124c09b5224fb0c4f0d3f48ca19ac8c01d6fad113ff4ff5ed
bf1dff324ef548e2d6b5edff339106
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
1627366cfc3f6a5f03427e82da2507ac69dbb0a1f465fd9b952b41cca4c34ba4

exporter_context: 00
L: 32
exported_value:
7cebb3ebb7e3a179d4bc569558dab5ddd965b93345447bfa960a7f95085cc93c

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
24ea07cdd37c3e227709d01dfa7d32cde3b41b3ba047ea9f1eb5a1b6e5943b47
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 2a61f6394036780e7c9a4048720ecfff7acde305f155a71a7d956c8acde848d0
pkEm: 049378f55db3a846ff081c6e0d9a5c578230433ddf48c54d5a904cd5c4fdb5cdb0
b906e54669d26cbd2aaaa6aa9359537daf9edc1f347d0c8642aea37c81972252
skEm: b0b589f32d2b7837f3ff0bf434ea651c10d453b4601ad21a077b9318ca6b854e
ikmR: 41a1f67731bd0f35a1a0db976629a2517c3e153059f8cda5c4ddbbd871d4899f
pkRm: 04847a90523be6548ae2d44cbff6a9c03f39d0c9b80148340ed65fe2c91761f242
27eb159b345edca7cf4bccac6ed81dd318b61cff00040e170fc7008b7fdcd117
skRm: ad630a5093f2eda097312af9f489a54e9ab556f87e5679787c279464118644d6
ikmS: 0b8c140ee89b2b8c317273cd9606c764b18b4ca191bafd196164b363d556299d
pkSm: 04b8c20bc8d8dd5cd5ab5798a3c31713886085cb22417a818cc5ac17be54b37c52
706f3a68294d885cbbd33a3b3bc1cb34530116554323b6b52a02c0d4f12e43a7
skSm: fd5d710600e12f484dbd411f7a552caa3cd677e02a3c1546227afb90c98eb154
enc: 049378f55db3a846ff081c6e0d9a5c578230433ddf48c54d5a904cd5c4fdb5cdb0b
906e54669d26cbd2aaaa6aa9359537daf9edc1f347d0c8642aea37c81972252
shared_secret:
93578a95e097d9743f67f84f8512aefaa57bdea3756426cbf2cc228359d0f97f
key_schedule_context: 025b8a3617af7789ee716e7911c7e77f84cdc4cc46e60fb7e1
9e4059f9aeadc00585e26874d1ddde76e551a7679cd47168c466f6e1f705cc9374c19277
8a34fcd5ca221d77e229a9d11b654de7942d685069c633b2362ce3b3d8ea4891c9a2a87a
4eb7cdb289ba5e2ecbf8cd2c8498bb4a383dc021454d70d46fcbbad1252ef4f9
secret: 5d1b621d67fed41f532dcd3e339ed73174fe7f12a0fc3ecf2dc1bc168ddc57a0
22202dcd38e377e280845d692be1ce111af492210a78548a6bc8561861738779
key: 4a182e1ec4630eb8f54fe3e5eab952f8
base_nonce: 2c2425c11f3d8b2f21351387
exporter_secret: b0a2eec2132a85375927cc01799b2f9d37d26fe59d552a5b881b14d
f60d53a92c61cb170a1c154f3664be8996cb779be7a2619515f4c5849533b6a2138de390
e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 2c2425c11f3d8b2f21351387
ciphertext: acd4eddf9dadf2d0dd07e0bedf1133c79a957277f2d109d6de6e2d99d731
40c02eed52ad3e5973c0b90a14de6b

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 2c2425c11f3d8b2f21351386
ciphertext: 25a56af68c15c858eb148c12f319e4fffaa0d99101fe20f6822be3300bdf
5a0da0057c21af274968a6955f84a4

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 2c2425c11f3d8b2f21351385
ciphertext: a2f53a93364a18a0cb01a5392250fc9385b07cbd71fbf0fd7b92a3e7f20a
ed44a129d6dd14825b13302c0fb8a7

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 2c2425c11f3d8b2f21351383
ciphertext: 363e6aee750cac9abf8201c6e9e1bb9cb1e086334912c5b507c56ee83c8c
0c6bee77a2d9a1f791644014285233

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 2c2425c11f3d8b2f21351378
ciphertext: 499dab2e6707f01fb4e428f056e0a34816e32d77bcc80b1ba8e145be5328
89f831669d3012f0e2c2576c0a7bb4

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 2c2425c11f3d8b2f21351287
ciphertext: 1ded56e1c32d570ec48718d2710a0fc70d2b359c29b3cc32f3cb2343313e
cacc7622ce89c25ea86a342e260aa2
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
8c7499c5add1ef3ad3f3e4bc961cbaefcabdfffb358c8cac502875d1ef40a15f

exporter_context: 00
L: 32
exported_value:
61f0b86dab4a73195848b1d1df1fa10aa17fefc82b9cf692832e993c535a685d

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
b6be89e802314c4bb3810db8867f7d60df8dec5e79584f7af8081fd62987bb68
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: b27d8f329d6a953aca9c8187e02e2bcab1e0641e58bdb761b2994e51451b63f6
pkEm: 047dfb108693ec62e2dfea08ff895687c2103fbe42df0ab874fa66f60283beda8c
720a6bacacd0825ac3ed5e05878c26bfcda25a5c20c892c4255b8c069b1676fe
skEm: b70f7661ea91cf428d8c345f2050d10f390bb03cfd71c347b6575e2dacc94993
ikmR: 68df99b60e0abc51fce4055a48a5c4a7aef89e8b03e458cc7be078bb0515bb0b
pkRm: 043c34b9126148da0c6acaefa1f60f0dcd310788f78630ba33b0d10a8bb5eb679c
8ed310e3a4e8e768835996c73eff91c2f7e42d4527ef864906063cb508bf1097
skRm: 11755a655c396e303156fdca380e4ffbeaa577ed4dbaf0a92c67bde1961c4437
ikmS: 4cd369baf0d10193895759b259429057380e01fbdaa704b0d8ed057c7d696c4c
pkSm: 040b13edd0322275648b812f1634cd9f151dda9dd892b2483efc1378078015fe74
71d7aaae32ee47f2a4efce2b3f12dcb3e0cfaeadf4efcd73f0718bedf6c10959
skSm: 7156183d9b592cfaf6634cfebe35049e605eb4bbc2fe36ab0b819dc34b2e15bf
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 047dfb108693ec62e2dfea08ff895687c2103fbe42df0ab874fa66f60283beda8c7
20a6bacacd0825ac3ed5e05878c26bfcda25a5c20c892c4255b8c069b1676fe
shared_secret:
20545df99d3d74c27dbcab138983602e75c857ee1cf74e5d83a15fc8065ff389
key_schedule_context: 03713f73042575cebfd132f0cc4338523f8eae95c80a749f7c
f3eb9436ff1c612ca62c37df27ca46d2cc162445a92c5f5fdc57bcde129ca7b1f284b0c1
2297c037ca221d77e229a9d11b654de7942d685069c633b2362ce3b3d8ea4891c9a2a87a
4eb7cdb289ba5e2ecbf8cd2c8498bb4a383dc021454d70d46fcbbad1252ef4f9
secret: fced0492dbf1e6ab3de38e73188a514d2a8c96896af15fcf70ef35230b36a39d
d976da673c5cfc88271e90f87f709c1722738a1d5b036060a5ee6a9730e046b6
key: 1ab3a0f20fde7375875e3cde87239a44
base_nonce: d42859c7198947ed53f21e6c
exporter_secret: b5a9e7b78914552a74079ca2a7c0cf5aa15c2555f6fd2d26784081f
347fbfdad140f8fe929d097e83431c1c12d6663476d67dd29d7d88521d0a4c2bc332985d
7
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: d42859c7198947ed53f21e6c
ciphertext: d5605006b0c87337964c9b348079a1da045fc461269996574cf6b9c60b8f
bca23f351ab8b6b185320281fb8344

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: d42859c7198947ed53f21e6d
ciphertext: f15b7c1692b662d6f515e282e45337a522e75f958e78ebc929b053171236
7c8a893fb336c21f7bd887ce9bedac

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: d42859c7198947ed53f21e6e
ciphertext: 358b4947f460265a7fcfaac4c96d3162d55dfd38cd1f1c1fde65782d4cc0
e315c1b9e6be33c43324d269ad2317

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: d42859c7198947ed53f21e68
ciphertext: 3fb0a9fb49d1c98150e50faa338c2d3fd81a6094cb3022d1f8acc15a0d35
930e91c278baf6e79c11489c415bbb

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: d42859c7198947ed53f21e93
ciphertext: ab6f00e0a5082e99c367f9635a6ba63543cf31939ba46beb572a69af2b5f
272788b539422c62e297c322a34ee8

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: d42859c7198947ed53f21f6c
ciphertext: 06075a79733d0642f079bc0a2d7362fb8466ac05bcb31b29c2ad8b87f905
c2a46f73d663d72294039f879fa282
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
f2fb2499f7747b794d92464fdf526ccf9cdc46a9582a1fa3ca8f99c11e79c1f1

exporter_context: 00
L: 32
exported_value:
8c6ee7e40e30f2cd9182e6d15e78bb0909743f9c2d1d9ab0573b257fb15457e3

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
43c109f9c52939a8277885d6d59a3c67576170972515bf5b299d807a5a201f6c
~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: fb7eaa056c7b37a26b262088a8a930b5b81afb5c620de4a3a09e9d508810613c
pkEm: 045474f87278e03b966d6b6cc8e16844dd2bac7537b49d22604273b95439ba9188
9f9827e81b21313330d0ee37a6d92f58dc121a0b410f51b3cda4741f41fe6ba8
skEm: cac3440ea732bc39a415ef9896874faa44a6cfb6e1c47d6b3f07eb632eb7ae41
ikmR: 48d7d639e577f8c1544c09547241e23b682aff3eebdf3cbd525e8b0d3b9da8d7
pkRm: 04556e729947756e39d8dd7e1562b30e703bbe8e2bd1c1eb06a41d399b257b6132
974dd28f7096a4527b0bb1c78fd7d57cd1c96c9b2e0e9e4b081361379b57d542
skRm: 29fc91eab2052fd50914d3751cbf2b8d64be7f9a90dc74ffc5661dd5d591eed6
enc: 045474f87278e03b966d6b6cc8e16844dd2bac7537b49d22604273b95439ba91889
f9827e81b21313330d0ee37a6d92f58dc121a0b410f51b3cda4741f41fe6ba8
shared_secret:
f4b1fa34bea6c1f00bec7c937b584c6e5db7aa0a944797fd9b3ba0909f341976
key_schedule_context: 00b738cd703db7b4106e93b4621e9a19c89c838e55964240e5
d3f331aaf8b0d58b2e986ea1c671b61cf45eec134dac0bae58ec6f63e790b1400b47c330
38b0269c
secret: b1d448921b63312b1855acebf6c95cfd234110c30cdaa880e7bcc29f1563f45b
key: 21e23a4a80f168f96e1e37e62d59443b0fee504aacbad16500b61c4f2f11a246
base_nonce: c3c1b5bc6bbbafa033f7cc60
exporter_secret:
8d51db90c0c427e2f7781c196d290e2613e11df8f873162d1e7c5bcd5ceaa431
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c3c1b5bc6bbbafa033f7cc60
ciphertext: 5991f6fa1d5cdd86c33acff54b48c1bd53179828e86d2c81b1eae5e78084
14138b0f7856e2294ec3ce2eb8f750

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c3c1b5bc6bbbafa033f7cc61
ciphertext: a83118a4605c971d1b5a671d9c2115d654804b967ed186eda8763b29e8d7
e321a9499dbd81a905f4d2641dd286

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c3c1b5bc6bbbafa033f7cc62
ciphertext: 184bcdaafd41f39d12187c8814a698cf8680364420c041afd587c59d2f2c
b7288daf4f9d8d99f900f5f2017463

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c3c1b5bc6bbbafa033f7cc64
ciphertext: 2670dedef0bef994e6a29663f64c4b8d4a6f4f7f6499860289bc444b909e
746efaf7f68b30e366f3f05c2200f4

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: c3c1b5bc6bbbafa033f7cc9f
ciphertext: b65624a32a6aec902c9b72340d2e751c9983ba6a53f849c237f65118eb63
53f1935ef623229e656c6f8834e6e4

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: c3c1b5bc6bbbafa033f7cd60
ciphertext: 5ae74daf74067540ea0ffbf25939abecf490eb408c234a8378dea53793bf
dacd3ca6b58248df61f4361bd93eb9
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
ed865a3f37891de6ef863f2ca7ffc18d683d834d6e3ab3b1fd20d4baa21035c2

exporter_context: 00
L: 32
exported_value:
79583b5a03b6e534fd2c4232e86f401caee6a27ff7bfaf1b4f8af29242e6f217

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
628a17aa69434c2c6a38c88f99e2dd95d80eddb12c015dbf0c9f7ace022e9da7
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 2199c3c0ed31a2e371536b5cb096fa312cfcf5045d93528e97f172e0f39866f6
pkEm: 04e552acf54c59c04c5a9a08a8a82ab85be854637377f965eec7bf73253821a068
324ee80eec4935631c4b45247ef5deb4c1697bec5f21d194918203b58fd9da4e
skEm: fb725c07a4dbae07958e4703055d80fc615d004012d8b8008a0e71a742b2efba
ikmR: a20a1180abaa697a7e5e7a7766b52a34139846a0cc0a67fb51072a9634899c44
pkRm: 04cc233a9ef705b0b172153e2a7c6ad3a85db8ca9c900f22c475fd2cb709aa79a8
c9ede32edc23b5b6c95114e2d4d38f3c251837906eae078ae730198c0d91017a
skRm: 86ac4af9e4853d1ac064819729eb4921239c7f3556261fbb92b195ae8ab48166
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04e552acf54c59c04c5a9a08a8a82ab85be854637377f965eec7bf73253821a0683
24ee80eec4935631c4b45247ef5deb4c1697bec5f21d194918203b58fd9da4e
shared_secret:
6b8fa7503995c91d7b4acec5a2a29f2c229899d4ca642bc34890f6325a895249
key_schedule_context: 01622b72afcc3795841596c67ea74400ca3b029374d7d5640b
da367c5d67b3fbeb2e986ea1c671b61cf45eec134dac0bae58ec6f63e790b1400b47c330
38b0269c
secret: d840c7faf2b7834555c15c90e5f702443e00ea87b8c72757a7d51fea795f98f6
key: 20239671743b55132374fe94e038e287327cee829a8ac65a16bfcaab74d30fae
base_nonce: daf02d1650097caf868fdae5
exporter_secret:
3a0dc288dd887d284b16ef869bd462201bb7be4f1d07dd0bb77a96c139b27799
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: daf02d1650097caf868fdae5
ciphertext: cc9f19634b89bee7fe7200dcbbb1441c44da0be5da01b9afadbbf96fc8f8
9407b0b6779501a87c988ce29430e6

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: daf02d1650097caf868fdae4
ciphertext: d455eef2371876080fe0b8547a67782e0b1a77ccedcdab9d2eb60e1b2d44
8fc96c2525c82a14ed00d58686cdb7

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: daf02d1650097caf868fdae7
ciphertext: bc25021ce98e22be1db3ce12fa379181fa164f021ec7755df22865a83e59
f3f60268bb7049cedd39426f1e8d5f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: daf02d1650097caf868fdae1
ciphertext: 4c73abb910dff5a8dcaaac774a11f23dcc42ff6932811e951f3bb5fad9d9
081da984961be9387a2c57d1be07d9

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: daf02d1650097caf868fda1a
ciphertext: a842c570eb24b0523760ae9566fcddcf09f54323ca32fe813d45c7bd71f1
6a2879d96f9db0d5b2f326ddf5ba6f

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: daf02d1650097caf868fdbe5
ciphertext: 020a10b8bc469ad581b1d5a522a822109bcd2faadc8792b5f7bf2f8b591c
9480845acb830eae6bb645f2724a3c
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
e2ad057a42de5ebb5b3f9a1a39722aad0c45b50b1caa34257bd741ab208f3302

exporter_context: 00
L: 32
exported_value:
b631accfcc1aa3f94768f93c1d2160d15b51e2579dcacf4e8e7a575f3e422156

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
fa298b1654b036c3198593bb114f34f84cb03ff1156034adf8ec4c54ef444b8a
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 819471f7db37b996024db13951a66632062df70deff35b58c1165e7adb25aff4
pkEm: 040b73ff934987014834c6453b6a8057a9217e03c3be7f0afcc74042f21be7d06e
3366e47f1e34ad9cc8a571142ba0e63d94e99fdc8c394b1651e424ad3eebd414
skEm: c330fe7e437bce2893901d2b5fd211df5e7d9ba8bc537b6986973ae031e5d46c
ikmR: 4e934b1f2b983a8def69de403cd014231dc63828f190ac40610dc1df1fa6d8a0
pkRm: 047c9bf9558dac5bdeee11ea9bdea36851146e201542cd26141bfbc7095244cee1
2d9709591b8c9b48363f203b812c5a84a44c31455f52f023fdfdbe13140bd33f
skRm: 7878ef8cf674617bd99058a115548f482eedbc0f526331e1ad21a021b5275723
ikmS: 3713f7fe362a9794576b8108c8b975e5b0b27d184b7474d4778850b0fdf4dd8b
pkSm: 04682a5e620301c971d107fdb8ea2ec48b0a29ddcc97f4c070dd007b506d501c70
5dfea55b24a84c24fea0111088158f94eebf371fe5d4eaf78b985402bbec87a2
skSm: a94a38a74dba292d570ba85574e2a8e5388b76ab0babaa8412af0527770cbc09
enc: 040b73ff934987014834c6453b6a8057a9217e03c3be7f0afcc74042f21be7d06e3
366e47f1e34ad9cc8a571142ba0e63d94e99fdc8c394b1651e424ad3eebd414
shared_secret:
cd495aed7822efe4e37d36373b96bb84b8acbf460a66032b9d68cf2166fab4ca
key_schedule_context: 02b738cd703db7b4106e93b4621e9a19c89c838e55964240e5
d3f331aaf8b0d58b2e986ea1c671b61cf45eec134dac0bae58ec6f63e790b1400b47c330
38b0269c
secret: 4eafd9acb4179afe4397feb9a17bb7ee618c030e98e4db423998256545c2943f
key: 69f67ea1071c9b7d84fbb48e2b121328dc31b9446595ec75bd68bb95ac13fbfe
base_nonce: b6ccfef95e7511a39ff2568f
exporter_secret:
658e4f017e9112393e4c924f4e192bfbab6036a4f7c328cf7b92e43fd18c9ea3
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: b6ccfef95e7511a39ff2568f
ciphertext: 732925e72ef5206e1919196589aaf5e49c1b9fedca8698b14691464f7aa9
05cd668313d43a22c948d486158a0b

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: b6ccfef95e7511a39ff2568e
ciphertext: 5b75bdf82c9cfead5624647d33a0c61d3483e32412c6167ad292235773c4
b62ddd5e4cde2b84ab93b425681c52

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: b6ccfef95e7511a39ff2568d
ciphertext: 8f28c74bea6a51ab544f053e4594f31b18537a37ab7b82c716fdfa3aae42
7c1e8421d9b7d6dbb6d1af8ad00ab5

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: b6ccfef95e7511a39ff2568b
ciphertext: e8d1604df574b10dbb8e0ec5cb61aa49bee9e719c826600b8c407f70fd18
61e67dc147364bfbeefdc1984034c0

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: b6ccfef95e7511a39ff25670
ciphertext: 9ec75016fe938b430e8554f615cf33dbb207ae5a35e22c36acb46d2f79f2
ea7f009ac8802c8cf3b45c20839b33

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: b6ccfef95e7511a39ff2578f
ciphertext: 0d05a4e9df5d6df00d11b7250334afa2e59a9df311d4d4c77ff6c8c3b50c
1822aa77a4992f142bcb3fb6c46ed9
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
59e55fa968d4ca15cac6dd964201ab8aa585f02fee9e3a15e1321f0f7ae06c4e

exporter_context: 00
L: 32
exported_value:
126d020174f14bfcf500b41ae82427806a8c9a4d0b0cc039703e29b4866dddc4

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
6871e5884b04115a0873b050d832135f2bec79ca040d4efcd18119dc0059d1cc
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 64ee759fe918e31343f346bf3e744759e9f3ab5e9f0cf0380f24c1e1cf602a3c
pkEm: 041497a2b065b3b8769dbcc620eec7150b22f87bf4e6aeefdf67d424cea9ba44a6
e204d754f76568a46dc4b42ac02220f757971856083de5e706e9dbd7626e1a2e
skEm: 08ac179d8262d267ee65fa0cb99ab9dc90b73ceca9344927cdf0cd86cb579b4f
ikmR: 3e06b1e6be9b26f1e7bcad8eb0fa4e474e3a9f85727c9cfcd03f721895b6e83b
pkRm: 0412bd166f116919f44337a960e0846543f57c619fe6a51ae2da406d7870226763
9bcc33e57b3ac8ee45b62e0ba8e457d2f2da29980d59f0ecfd41d3c008de1f5c
skRm: 98eae9ad82a6caeec240659807bda3515451d1766abb3ebe7b85ef0cde6eda75
ikmS: e57c31b98819771f4ce8f25fd0ac350077466754a2c15aba75166c890e30d9d3
pkSm: 047ce7fb66245cb7323c637672c9dd47473d3e1a1912419efc516d339998415d2b
9b6bc417275b4fadd6a60ca35a247e681b6ac8b2ce526d5cc9ff792dcec0190f
skSm: 5f1ef9045d8c2b1aad955da9469e9fd48adff0569a73499109ec2b1be55e7283
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 041497a2b065b3b8769dbcc620eec7150b22f87bf4e6aeefdf67d424cea9ba44a6e
204d754f76568a46dc4b42ac02220f757971856083de5e706e9dbd7626e1a2e
shared_secret:
d2b7b501e921a11256e244475d4f870d75eec647e9fecbbe9c213ee1705d1fc3
key_schedule_context: 03622b72afcc3795841596c67ea74400ca3b029374d7d5640b
da367c5d67b3fbeb2e986ea1c671b61cf45eec134dac0bae58ec6f63e790b1400b47c330
38b0269c
secret: 50fc9ce859266be2cbfab45ce10c42111b2d836b21279b584456e76ab79085e6
key: 99f8b2f957c787aadef8fcefa5f96d197ee71ad2bbee65dce5386de3c3830771
base_nonce: c7e32cf153859db8d8e70124
exporter_secret:
a015526fc2c421bb959d818c4d4f9b07d57a653c48b98ddd03a2dd980481bfef
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: c7e32cf153859db8d8e70124
ciphertext: 0856f26946fa2e9eb6c7744dbc938fa24780a56716caacc22a80b2771e0a
1ca625dd24acf9056217580603fb30

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: c7e32cf153859db8d8e70125
ciphertext: 8c4ad8fb6f99c353ecf32216937457549ad9066fb949090aaed2d6b9974c
f86138bbf59c5582970fcea797a649

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: c7e32cf153859db8d8e70126
ciphertext: e57a1247a01e824480cc3c36cf1667ba5b416087a31bc8ab4a46efba05dd
451f45215c51c608c278e18192519f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: c7e32cf153859db8d8e70120
ciphertext: 94f56f790f2b932f9cdd912a9d7176420d62895494cd22d68f16cf51d5ae
968e76c294b422d46217d7b650ba90

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: c7e32cf153859db8d8e701db
ciphertext: 7b1a98cc7442fc2e32951c416f7c63abf2e4552a9fbecf97e63b142510fa
5b308a866c583fa7d798995e85021a

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: c7e32cf153859db8d8e70024
ciphertext: 788f0712690d0ab43910f14c01a2080ecefe5f97037669e6e64afc2baf88
a5fec1180d091046c64cea09a9075d
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
3c27fbcbf31d1b180f9b763872f24cc19b631d8a6ab1f70baef515940c1f78e0

exporter_context: 00
L: 32
exported_value:
ef4907ab824c885f949047cbb38b1a12b1b602e4a028cd7894a93552ae82d341

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
e286f3fe9a4021f73e490be944e8326247a893ee3d62670eec5ea69d5d8adc51
~~~

## DHKEM(P-521, HKDF-SHA512), HKDF-SHA512, AES-256-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: e816363fe792e5285c816babb10ff23671782810a4676777418043488f83c8bd54
d3b3292bbc3ae977feda48a25c62f1341b5cce8f65e5b0451e46223d18d0850bdf
pkEm: 04019780208c86fc4ad7c92a21874d2fc1781ce5fa8b44b3f67011bed7712a673d
ce143d0e27a51afb9ed99bcb7736f4e63cdff39dc64e1481365a9bf789ba59c2ddc7017b
96c78d572a05b838cd2fe01a497a63340a91d21d8d9aaf9852ed42a5ce690add161dc526
9396ef40d588b10eb769f0ad01e33e171375510c81fa589f087249ec
skEm: 01140c274344236fcf0db3ab2f527ded8d32770510be80bd772dee6bfe0d3b65ef
b3a8ab199987170be1b583930effb0fa6248f69e1052b94636e431831036c18c83
ikmR: 97d30bf785894d356084d4659ffb4e1d9c60298a9909414eeeed827223516a997d
2863e85fca294e9d05df298870f442f5e75e86b65c44f06d16e4709d1a0eecd533
pkRm: 0401e96efacb95cf7b00a615f0f56673a567f13c5fcb77d29871bb72fc9a3f8711
2929ac05c423af1989777231b4815451117c09b0a2435caae849238b841be8aa59920147
439155e148da785331698018614aafd8026fa0b7d84385402301a5b8d5a3f2106973f088
f302fbb84d76d8bec459a7dda8378a9f32ef21df757c6f374206d9c3
skRm: 014767fa05fcea80677c76b2be2efae6da8e36663998d2f7480a4ae9e38e78d993
d2fc6e35a7cffa937e39a7bd907c0c14fb385e187d84927b809e6ae88e109df0fc
enc: 04019780208c86fc4ad7c92a21874d2fc1781ce5fa8b44b3f67011bed7712a673dc
e143d0e27a51afb9ed99bcb7736f4e63cdff39dc64e1481365a9bf789ba59c2ddc7017b9
6c78d572a05b838cd2fe01a497a63340a91d21d8d9aaf9852ed42a5ce690add161dc5269
396ef40d588b10eb769f0ad01e33e171375510c81fa589f087249ec
shared_secret: 5473f7360bbc31bfcd97fc230e9813bdff076384a92f8495e5c3bf395
eea7876a0dda8f8afa960cded0b28029598cf450abeb3a345b6b26aeccfe3301d3ed109
key_schedule_context: 0083a27c5b2358ab4dae1b2f5d8f57f10ccccc822a473326f5
43f239a70aee46347324e84e02d7651a10d08fb3dda739d22d50c53fbfa8122baacd0f9a
e5913072ef45baa1f3a4b169e141feb957e48d03f28c837d8904c3d6775308c3d3faa75d
d64adfa44e1a1141edf9349959b8f8e5291cbdc56f62b0ed6527d692e85b09a4
secret: 5484edb6628b2843005a69b564f21c2202ba0062a7908bafe4663b36e9fdfd3c
dad1ac5e5421a6a46b7787ba1ae056d602661a81393111288b756ecac0e8d563
key: f9d5401a73975715c3051aaf914f0243b9ed5b2eaddbe90515421447f3389261
base_nonce: d090db22e1cba6b040109b78
exporter_secret: 74fea020b7f23573f864961bd6999c9bbff887e6ee9edd1f7939d54
42120dccfe2d15251f9ce66225c8541fa6f5f62e398496fbcb5f1954a1cdb287f1ebd243
3
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: d090db22e1cba6b040109b78
ciphertext: 605ea698d33708d81bd09253936c6b3ad43fec844056f6fedef8b1c06402
8f8e241cd5b0f9f2bcf1f4800e8bb6

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: d090db22e1cba6b040109b79
ciphertext: a34f2b0adcf47fa23470815cef9337cb00e399035252e157a2e5d3293d69
ffcca4f3062311e84b9167876e0742

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: d090db22e1cba6b040109b7a
ciphertext: 815621593ff6081ad26cb03b383259a23efb7df4a55367c9b19ddd69f5da
ffd502003b76c366707cb23248f676

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: d090db22e1cba6b040109b7c
ciphertext: 33df6755b98a4b9b143cd048d12919decd86c9db41823e78eef57a4b0812
a23b9cca3dc6cf90ebb1fb553d1351

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: d090db22e1cba6b040109b87
ciphertext: 81c1bcddfea2735a552384b0aa438ee79e2388b6b8cb7d11aabf1324962e
2730e3835a32c8a951ebfb625553f5

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: d090db22e1cba6b040109a78
ciphertext: 6dfe4d4eac61f7240db8d17bed66a5a01b5c8ddc4fe3561df9451f59a0fb
c9e95cfe4fdb18c42804ee43c5cd24
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
7f0e236dec123ddbb1c52cd94b5abe1784c630d449f38d714dc7c36b9a34c192

exporter_context: 00
L: 32
exported_value:
e2f9eee31220c0df0fc6a1beafa76397aa9ba871762950bc7a3090d661429edf

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
9b6ace05b4a9af351665ee298f8b5a9154794719815252e9007e0e25ff396e3d
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 224a91601641db9b9168e789b7013da1836524ceb32cb8be50e1a945525a3dc2e4
0dc97d5bbf77825d8783b8f00fca99e73aab428afdf5db70b04409bc890d2a0dc8
pkEm: 0401907477e9fb34b84fffcb8ce639a11aa84b9c172de10ce94f52fb2417830877
73384442c14fc5a0f649c7b933f60ef5b25b71496172d0987c7dd4af7bf5ef598c4101e6
e1160075e4af399e7efa16d6d2b648e6a61ba186e833883e00e8e493415feae02418feb3
765e52f03aebd2660fa298f538b55cbbc0f7e47c1fa5e4c66e183423
skEm: 001280499c4f30ee97c11270a262cdefd820bfdeabf23271fb5f80a5de977583c6
af41f5c2d0362bb3f201f0a710ee21dc58aa849bf671c0716803d60a73af578fca
ikmR: dddaaf72ab69d45ba6a57b962a7a129d5234d94dec44188b18f431bd5b03e2cb4f
58cd77527816ef41022bcec8e8dfdd2859fcad61ee3034d1352e0a937898c4c6aa
pkRm: 040103697e335db54caedc8b0e5aae2058fc294d8aeed2fc816d6bc5699798e29b
57f8d9ede6d6040f12399cc82c9b1562c67cc08fe0edfab714a3b96036abbabbef1500a9
30bee8a346d95b2fbab42128e76cecf3d7b5af649623cf566ab394bcb1480f61e2b8dba2
a1af8016f8811180863c6359a6121eed4c41159a82136f66c429c97d
skRm: 00f58141be599a80226346673453619b2e6dc81c39c000e9666b8baba510b501e7
440bd136b8aec59a713376d0214e72a78e2588db37a86f2cf03eb19b387c82e146
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0401907477e9fb34b84fffcb8ce639a11aa84b9c172de10ce94f52fb24178308777
3384442c14fc5a0f649c7b933f60ef5b25b71496172d0987c7dd4af7bf5ef598c4101e6e
1160075e4af399e7efa16d6d2b648e6a61ba186e833883e00e8e493415feae02418feb37
65e52f03aebd2660fa298f538b55cbbc0f7e47c1fa5e4c66e183423
shared_secret: 65bfaa1a2451c8717c8b74613242df2b661a5ce5fabe26e36bfd35a2b
40081eeedc7710d9576087dceb796e0f3d2260f739fdd5ed4d28fc7218f456a859a345e
key_schedule_context: 0124497637cf18d6fbcc16e9f652f00244c981726f293bb781
9861e85e50c94f0be30e022ab081e18e6f299fd3d3d976a4bc590f85bc7711bfce32ee1a
7fb1c154ef45baa1f3a4b169e141feb957e48d03f28c837d8904c3d6775308c3d3faa75d
d64adfa44e1a1141edf9349959b8f8e5291cbdc56f62b0ed6527d692e85b09a4
secret: 2b7a1c4f3bd3ac40f5a389fb82affc8896d4527ed02e38fe04e2d69cc039bd74
6b3ff158aecd9839056fe55afabe7953b7871db735a847fdda09d357a825002c
key: ed11fdfa7c3dbd5cbac3850b1311c83acb3ac7ccc2aa8df72028c12955b3c015
base_nonce: d66f2043c916d651b70003dd
exporter_secret: a37dcdf7fc6c16c65f2e93d8f7cb20604aa20b1adf868824370faa9
f25c918972e26e932cae22016c2cba0b1a125c0450cdf6e4631d393a490b478e6b1d2b95
c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: d66f2043c916d651b70003dd
ciphertext: fefa1256b11ee536994482d1f0715ed10a0eee65ad7fbca49a80ac09d232
473d25e2e6fc2f8b91af42ed229210

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: d66f2043c916d651b70003dc
ciphertext: 4fed35f123a1d2ac37568a2571cc9af147ad88d81afb245b6f3af92f4fa4
383093ab48270a12a6a32cde904d09

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: d66f2043c916d651b70003df
ciphertext: 28b6b8e4a4c7c0e30e46d613717acfb4f20efe287bd4b202e7f9b7066791
15b2409b2469cb1639302f171d59cb

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: d66f2043c916d651b70003d9
ciphertext: 106efd243ac0ba5b78bb32b18bffc174309c1f29ff9b0b4c6112b4c2b4dc
b6518cf8df060b9ac5ae20412af7e5

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: d66f2043c916d651b7000322
ciphertext: 0a1464e1deea0d04d58eeaf64355a074f058fd6197eaab16affc8439c766
6a28ba04309d70d47c2c4cb5962a7a

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: d66f2043c916d651b70002dd
ciphertext: 85155357c1fb3146ccb9ef38bf057f839d9ae78553e9d54c7500ef004ec5
77ba7a9164947c1fd1cf927ec81468
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
21c37d6bbbffdfd63cb13da378e3af595f22a60efafee7ca8fa7a3cc0403a4a8

exporter_context: 00
L: 32
exported_value:
e6549454cfae1c0abf245081ed6c0c31a6f390af73575e2100a8cc02d43890d4

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
97d473ce06d4df7e5b2cc7cc7e79acc27e26437806b5e6307a8ab7cbb3b3966d
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: a2066d90b60a99fa770935b400c313de99f2efdac0dcbaa294138d9d0a6e670017
d918935e77cc1f81ec87d556a49b82a7dd5d9bc7976b38578c3973648b8befb237
pkEm: 04016ecd49f195b828eb60cdd003c70339f1bda86d80e9f40a417599875df0d970
b7a49721c146fcf8b892fb6f5482d89dc600221a8529aea433f7564b88d835ffe81201ee
04e1874783e474be670fec355e83c31a59a0b0060f70229b946ab4c9cfbd1c6217cdd8e4
6c038f7946868add31a27ade16f058c8e11d2fac40d428788e6333e1
skEm: 0110a353aa912aa4316ae7f390c72fd1be87e2f8adef8fc715107be338b248085c
862cd9237ce93744211f36372d3f4bfc2eccf6790929ece3e41373fd41fc0d18e6
ikmR: 3000d59fcb9030f3785317a01abd90609edfa89100277dcd4061f617d253878ea6
c58f1b7b7a87390e45eca1d10c18a9ca9fcba2d60520c78b0f781d57f5b9e3da5b
pkRm: 04016636885f9b083a22dc5fc0a6e1fdd8374005285d6082dd7e3b7ae5a4fba766
df086d41f63806d50d28107ba6e3b3439f72c80d91b89418918c88eab7678e5d0e2101d9
d6ddcab97f941cae455d74b95bb130c403f030a72fbda406dd1a2837b1ce2fbb1d0f7b4e
713a18a01fd26961480f0fe4ae86bd261a3c4b2a8e92c107612b3e29
skRm: 00fdec906e9b139706f2777050e29afe27b48afedd5b1fef21114412cabbe00f3d
d3f3fd8bb7d1f3afc946f91627589d2b19947afbbd8c77c6539d57ae67e0f5d7ce
ikmS: 72826ad3b9dc1cf81b08939fe462009ad4e38b23345faa32f1e51a95be0b469766
7fa953fa4361b52f0fd32d820f9ea0f3cf5991773f739ea9a624720d2c1cf59e72
pkSm: 040007920d5e02b64b23c561191f82423eed25c5790d4cc7d91c46ef130c05b672
7768692c1ad5dc8617449631c09ae7fedb20530631dcbbb0d41101a00bb997a2557301bb
aea1f4e08edfd1944dc790a6307c78fe8dbd3dc6598c3fdabe3fe69062a40d466e7b4904
506872fccd1fe7d69002407b466d95a1d433a137fe4ee0939e2c1430
skSm: 01e5e1966266232e4b623a59a6e3669dd11ba87b890e0100dcc2bed879d4b2e4f8
428e4a634cfbe7705bd8756a728c7f438f85396dc7c1db0ea631d68c33ee703e6c
enc: 04016ecd49f195b828eb60cdd003c70339f1bda86d80e9f40a417599875df0d970b
7a49721c146fcf8b892fb6f5482d89dc600221a8529aea433f7564b88d835ffe81201ee0
4e1874783e474be670fec355e83c31a59a0b0060f70229b946ab4c9cfbd1c6217cdd8e46
c038f7946868add31a27ade16f058c8e11d2fac40d428788e6333e1
shared_secret: ada05211d7306ca1acffe68f3cb8a509f5236022eda5e8d3f6cf34383
3a67b5945b133d2d0870c08a32e64f4059bea0067e48750afe3a6c5505c6c7be7bb8d57
key_schedule_context: 0283a27c5b2358ab4dae1b2f5d8f57f10ccccc822a473326f5
43f239a70aee46347324e84e02d7651a10d08fb3dda739d22d50c53fbfa8122baacd0f9a
e5913072ef45baa1f3a4b169e141feb957e48d03f28c837d8904c3d6775308c3d3faa75d
d64adfa44e1a1141edf9349959b8f8e5291cbdc56f62b0ed6527d692e85b09a4
secret: d33c12dba50e4088470dfbfbfe3355a94e9cd43fe4c53cf44713121753dad4e2
5a85b4746fb9b8bc7630ef036b88310d4613136f92958737d07eacd5302ef372
key: 619b814753bd1b378512eea5454bb609b3388a16170c5e02d8fda0f69d8f0415
base_nonce: d563f1f3b1acfedd2db1df54
exporter_secret: a240e7feff6dbfda16bd103a46d970acaef462861009d9807afb358
6f7fb223722c72c609c97b52765f69f15eae6f9104630fa093a4e7da978dd7370badf891
6
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: d563f1f3b1acfedd2db1df54
ciphertext: 23aad556ce6ea787bb577b581c6444c0efc5bf666fb1608acbb9f9874593
58fd0e1dff1971ea7dbde03653d225

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: d563f1f3b1acfedd2db1df55
ciphertext: ab54eeaf0c82a75cbad38caab94e953895d2a0d69d38570daec755d158fb
7fd6dd768eb6846d84446ba19c86d2

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: d563f1f3b1acfedd2db1df56
ciphertext: cf7a40d514c3044ca4d5ad7cec0aa9135a2a63eaeba7a75356e4ab5b9c6c
416ca892f069780ee301081fd7f80b

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: d563f1f3b1acfedd2db1df50
ciphertext: a137ac6b51a88344ca1e98c85ce87967a55be99ff4e9ac0d19506f1d8a5f
b4631542f579922df9e7d26b9cfb84

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: d563f1f3b1acfedd2db1dfab
ciphertext: 99e1f745d13f516f11c348e16191bf8da37eb9d51986f3615ac42f606b65
fe2517d870920ec94897753e67a1c0

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: d563f1f3b1acfedd2db1de54
ciphertext: ea0f4a5e88b9f6f7db1ef33c8830d2df211e23d9b4defc1583dc9cd569c0
ea27b6fbe05d09d490e0674ef33e64
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
0e543a305adfd1c63b9282a2b21d8882d8e5f1471ec9b6480fee4323c333f7b2

exporter_context: 00
L: 32
exported_value:
73bc84403062beec5aafc0b1ea16ac3cffca6f11307f36fb77ee941d51030d7a

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
fc3c7a3580a40f036beb5ffd097186dfa9a6a42215ff6fb99f3d55a240cbd4dd
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 3d93fa4bc180d0924a1544da5ace5a2471b0e61f24f125a44ed8e66878eeb18298
39b3b0bf5f13ab7169ebe9bcaff6b269d16ce730a95eee774df313d16e56c2bac9
pkEm: 04006ec798001fb2283f1c4196bf598d4c8f6b6e97059dbc24ba4452bf109e3897
408703316a84d95d44241c7d1e7d68ce54ca2f83b6e3341a9f45e7fc668f880aafc00079
8407b2b3ce8861a205cac29005a25a0ff14bb57dc5bdd6163a85784f9e55afdb6e9421c7
f6eb43f15a934340ca5b9c80348612d88b9419d4b728169e3611ffdc
skEm: 01998bf2f5ece296ce4dc2d19def60aedf08b9ee7cb560aa275678597f5fc27df2
facb148c6473e5a43f433e2e6155657ba39ce8778171578e7f7f4484a9860129ce
ikmR: 0bf005682436797755ecc073e150fb0a55e7e31a8a174b3a3ec37727eb532f7213
5e9b214ab2df9eecf063f2ff4d01062f307f4d5d4c54cf759ea1ec279b4cdcdfa8
pkRm: 0400e8fc411802613357defec521e5ea9c9a0a133813492d768d6f405b473d0e98
6a965354b7cedf14624bf3d43ff1d72ffd96687046ab25f5c03cba3defd36748c5a2001f
e95e00cd31323f4d4a1ae780771c0f05899fbe41e9aa68ce56b5804d18ede28ec60e030f
fa8a30d349abaf83fe25d909913e41a43e93ab50588c685cb0dab648
skRm: 00417cd786992c353304d172f583b1ced52e51a9fc4156a9e12e28ef419304fc34
311174661c5762fe047ace26877a481cf3bc35c2d59115d06c1c63ee4e3b397431
ikmS: 09c98e0c3674e6039bd53a8e420c70375c7f5c218f95e03be6fe9e20a0d4c7376d
aed12e322c83a3c3d06bbb27fbfa12a4355efc38016848b5c135342146634308bf
pkSm: 040166796e83c8c8185e3032c05868e0899218c2ee957e25883ae04a675d4df632
e5fd461b976617228acfb41521da294d105238e0e695bfbc247750e1165f3c54c6480023
7ad55f4a7fe21369a113af37157aebd588c5f44861388a63ac84e043b1af9788a0c68725
ea5adf45cfdd605da46f982d897a349fd236478c808d77ff8fb77d47
skSm: 01a02331bf17776205e2ec587ab77538876110b53b60943f1e43354d8a4cc0a920
7db53f2cd30ddfef16b2d8eb00b9ce719d0a872f843663d206407e8317363ef734
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04006ec798001fb2283f1c4196bf598d4c8f6b6e97059dbc24ba4452bf109e38974
08703316a84d95d44241c7d1e7d68ce54ca2f83b6e3341a9f45e7fc668f880aafc000798
407b2b3ce8861a205cac29005a25a0ff14bb57dc5bdd6163a85784f9e55afdb6e9421c7f
6eb43f15a934340ca5b9c80348612d88b9419d4b728169e3611ffdc
shared_secret: 1edee2ef179dbff88626c61e674232375e74a23d07acd64e4b38002ee
4adefb91870fddbe73c29cfa75162c8ecd1486e13acf3bb3faeb42215c7280d085ac878
key_schedule_context: 0324497637cf18d6fbcc16e9f652f00244c981726f293bb781
9861e85e50c94f0be30e022ab081e18e6f299fd3d3d976a4bc590f85bc7711bfce32ee1a
7fb1c154ef45baa1f3a4b169e141feb957e48d03f28c837d8904c3d6775308c3d3faa75d
d64adfa44e1a1141edf9349959b8f8e5291cbdc56f62b0ed6527d692e85b09a4
secret: 7e0e7a1b79f3b85c43efaff32ff94a8bd7d400a6641e4a8cfffdda02231938af
d2868884fdae8cf00c7d9841c885f577f2b17e1f44c0b93cb3f846d61c515c04
key: 8862fc5710b99d41b2133f0d5e886187eb4e3f73fdc3180425b412fc7386f2bd
base_nonce: 2e36a479d64ac4232a12a5b8
exporter_secret: a910164749ade23a45fdb8e239d8c441710d99e7c055030b13470f8
453530af38cff0800b345e227e68c96f849b64dc29bc86f151f3490cdd5cb1ba0249d9b3
2
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 2e36a479d64ac4232a12a5b8
ciphertext: 474bf4ce4682f0e6c11712c4b4f57f6c2f85196a45b73c1fd0db3cf6c177
0061ed06bcd6097c5d2cff5f80a6e9

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 2e36a479d64ac4232a12a5b9
ciphertext: 19bfd94ba5267e348fdcda5b1e862b3a66cd00e73c2f41546731cf24843f
795a23e75e7183c6e57f03d97899d0

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 2e36a479d64ac4232a12a5ba
ciphertext: 22913c7171120486aeecc6594de8cc13eb17c9fd8d1ee5f6eeabccbc40f8
6058091f2054fe0e9d113e632ff764

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 2e36a479d64ac4232a12a5bc
ciphertext: 0e4c2b6c9b4dc034fd98fb57bd85227806a535317d2e071a48007584b823
26892ea15cf080343998cb33b4b2d7

sequence number: 255
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323535
nonce: 2e36a479d64ac4232a12a547
ciphertext: 933d70d98beebb1b317bcc3a98006dbab6554027dff16c05e87a70ef013a
c964f7ddc81b496745e8c8c6b66344

sequence number: 256
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d323536
nonce: 2e36a479d64ac4232a12a4b8
ciphertext: c3e2d314c27db64c690b5478f28afb0a0fa82fa3deddf74b40f09af000ea
3cbb84a16bcea17dd05f3232d54017
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
05e8322356e220063fbc977f3ceeda43bc5a281764fa5099c5ff5d4192d36c1a

exporter_context: 00
L: 32
exported_value:
cc553f01d058f66c4a43a89e26ed641732cdad3e4be37e8c57a5cddf2bbaf41e

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
0fa7831241be8e7ae08efe5c80bffc69635c4cce9659120eed856eb2a5c13274
~~~

## DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, Export-Only AEAD

### Base Setup Information
~~~
mode: 0
kem_id: 32
kdf_id: 1
aead_id: 65535
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 672b9a45b089e3149259d5074aed7316085e0fa357557f96542df9a8ef7f0094
pkEm: bccac63a74990618c9f728ce74648c5f1c7b95a65169be730b16b1d52dfcc279
skEm: e2e554825f3a0e3af138e50d0e5eb2aa0ee13c382647ace1c0b56c3bfdd7115e
ikmR: db6719d2a84eb23c301cf7a9e513255e172b96507e893c870ffdc7ed30fa68b3
pkRm: 42db039c794ce1179796e9de4207cef03272e8c1aa81b3b7c0ce55d7bcad7d32
skRm: 85e900c2a99ccbd9ac8393eef0ad0dc89171d3bc06871392f585a7d04389e342
enc: bccac63a74990618c9f728ce74648c5f1c7b95a65169be730b16b1d52dfcc279
shared_secret:
86f8aa4918c61424b73cd27ab1b3ff72b3b304b6ce76fdb3c23caa0bca71e8c3
key_schedule_context: 009bd09219212a8cf27c6bb5d54998c5240793a70ca0a89223
4bd5e082bc619b6a3f4c22aa6d9a0424c2b4292fdf43b8257df93c2f6adbf6ddc9c64fee
26bdd292
secret: 2b0055c4008219162862cc46ef1cb2a78176f86ace2605f5b016be0fcd35eb16
key:
base_nonce:
exporter_secret:
832e9c7b8ead61635991beabc2968ed03f104c5847f8f2cb34c2be76adbdf8d5
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
fe02a379332a705803fee57efe0fed620a25ebaf25fb9a9510f85609776ec722

exporter_context: 00
L: 32
exported_value:
c16ccbad5873154c2047fd209edecf9fa13d9d9d941caff8c67a866181967c92

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
c564218a9fa1ddd88f5d528c7d17b76280e46be7836cc4f73dc4544b3f6cdf70
~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 65535
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 8cda8373640c2c18cf8c4161b5ce95db3f0c327a54fbe60736ca07a780549638
pkEm: 9af685d82d29f90c403422a34c7b2b5806d76f4b8d8716e2f2dc47e9189d205b
skEm: 8e93151b071a49914727729bf624621e86d4bce87d7e9a80d4c70b2e58db83fc
ikmR: 13f9c7e10a6ac346d14c794fbf246c98975b7902bd8868874796816b8662fb33
pkRm: dc40108fcfb0f05271a1b4341e1c08b6c9cc9826bd14d51dd577352cf230de77
skRm: 76594938e5307ffb18532fa9ca8fdf573f67ce632eef960b20ee2b1370aa0933
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 9af685d82d29f90c403422a34c7b2b5806d76f4b8d8716e2f2dc47e9189d205b
shared_secret:
e2b031c9af49e904b19b676228f8cb481f79f8f986d62c141509120ba214fb12
key_schedule_context: 01446fb1fe2632a0a338f0a85ed1f3a0ac475bdea2cd72f8c7
13b3a46ee737379a3f4c22aa6d9a0424c2b4292fdf43b8257df93c2f6adbf6ddc9c64fee
26bdd292
secret: 79df11288b538645df6f8634ab35bbd6770a82162c1e75ebce576e3b8a119690
key:
base_nonce:
exporter_secret:
d7caf3ec9ac7eb7bfe615a485be6d7a4bdfb74ced5ce34fe74a3cd2c985f22b5
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
4d0e8d42d1da00ccc50ef48dd98a0985389bf5660e26481871fc2331e2797486

exporter_context: 00
L: 32
exported_value:
1f084ce14f6569424132b3d4f699421ef9c93d1ac7b09f891b9020296ad87b65

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
d958d365d73b603c7fdd65f87ece8ed8927f69e697979b6cc33dfb2e834af086
~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 65535
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 11fe27f20fdf5d43272071bd00e61f050b26a4982ab6c39bf6de52c8fdb655d7
pkEm: 91dca833fff9f568e492ec39cfc175fc0d0e3bab7dc28f54655ed7550a3b6b7d
skEm: c66fb577ebcef8a0a34a4982892dac2921d7b1a7e6b402999a38a2ba5cffc4db
ikmR: c215df8ce3c13bc1bbfde414092940518990802807b16af1d32c68fe1a6a4d12
pkRm: f4592bf51f69f42814d18de23a5784da02f1e46e07c1499db687b3d04ecb7909
skRm: 7d02e3fa630b2243aa5e71fd74a9b1a252460cb56dfef6a05f0c0bfad044b07d
ikmS: 8759aa097398ec41b8a2fc3ef9b8e6e46acc2cba2838415910753441b2db35bb
pkSm: d8b9ac93315ba3c72ad6f89b2f4b9a71d59a82279d03c1e18bd841d73d503062
skSm: 04a3ae847afb2a516e10c7337acd92834fdef069826a9c261df90a7e85a55d05
enc: 91dca833fff9f568e492ec39cfc175fc0d0e3bab7dc28f54655ed7550a3b6b7d
shared_secret:
f3de7882324893bade69512c5e3a82886edade4c94620b6de16c14d0d07e55f0
key_schedule_context: 029bd09219212a8cf27c6bb5d54998c5240793a70ca0a89223
4bd5e082bc619b6a3f4c22aa6d9a0424c2b4292fdf43b8257df93c2f6adbf6ddc9c64fee
26bdd292
secret: 740c2884b0440ff4c84d331bd2fd6ef3c67be02808448ac935fe1ef4c5851845
key:
base_nonce:
exporter_secret:
b32803830e8c866d1d9e1cb9f8fc1572a95fcd6fc42e8b1838a2a95b29edb20f
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
c3057df633abeb2f03542a5362d063c8c58edfc261b5e60cb025f06faf295a67

exporter_context: 00
L: 32
exported_value:
ba65eb44590bb901dc2d8ef374447624be46d67d2f7ab69b27372497ed52b169

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
13fbd2db2ce0ba1346c9b6340bab0150bfeb127b4c3759cd63065292bf673891
~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 65535
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: f2fc7dcd56a4018074b5b425fe14bc09c5f6e5fb849e401102dc36d980858569
pkEm: 9544a55becdd322c02fbc4f78c94d4a5d3b4728a4e4dab5d43e02bd428aabe39
skEm: 9b8783dc16111714d264e519feea65b2a5fb5b15de8cdebdd7993954e8d47cce
ikmR: a5db29ae1d0bec5aba6b29bd6bb5a3dd45265d262ef21eca81d9444857c40784
pkRm: bb032fc06eff8a62e8e353c33efb2ab1f5e3b8542d79b7d6a2041e920cc14330
skRm: 1952390f1b32aba4fc1298639a995d4c68a46d0c238914955c515034b118aee1
ikmS: 5a0482963583ccc77b25c5bf2bc621f136b0872fb989ac4ed19f8ce8d07cbdbd
pkSm: 8f88e2a7dac49d07c73751e852288515566fecc767cdb6d53dee58047edc5f38
skSm: 99104f871ffd94dc07de5ed5da1ffe406a9a1a3a18196e76a23fbb50ce303ee4
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 9544a55becdd322c02fbc4f78c94d4a5d3b4728a4e4dab5d43e02bd428aabe39
shared_secret:
08d824d0dd8c6ae128b7a4666d3330f9c0ce8a225384c1e1cbf57daa44eca846
key_schedule_context: 03446fb1fe2632a0a338f0a85ed1f3a0ac475bdea2cd72f8c7
13b3a46ee737379a3f4c22aa6d9a0424c2b4292fdf43b8257df93c2f6adbf6ddc9c64fee
26bdd292
secret: b3f560cce69d667b5f5dcb302723eaa01e9dcd5ecaa357057bfe52ec2ac06957
key:
base_nonce:
exporter_secret:
48cd82170e08699342b503da5f7bb5b8d4d35ce6ac0688cf75438709bfc1d525
~~~

#### Exported Values
~~~
exporter_context:
L: 32
exported_value:
57720a6a42de799f324aee35520a932a07628bf3a916bc8572f2e0b22ef6ffad

exporter_context: 00
L: 32
exported_value:
c431eefc3c807fec80c4ab4edcd68f166744a1cf0117f74930743fd3ca772398

exporter_context: 54657374436f6e74657874
L: 32
exported_value:
776298ffdbdcd801077935deb54a4fbdc5c03d926ffdc1ada3cb80d0ff089381
~~~
