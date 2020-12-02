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

  S01:
    title: "A proposal for an ISO standard for public key encryption (version 2.1)"
    target: https://eprint.iacr.org/2001/112
    date: 2001
    author:
      -
        ins: V. Shoup
        name: Victor Shoup

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
    target: https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/f4b81ac3f63b057f99f3e0cbd8a108dc0495191a/test-vectors.json
    date: 2020

  keyagreement: DOI.10.6028/NIST.SP.800-56Ar3

  NISTCurves: DOI.10.6028/NIST.FIPS.186-4

  GCM: DOI.10.6028/NIST.SP.800-38D

  HMAC:
    title: To Hash or Not to Hash Again? (In)differentiability Results for H^2 and HMAC
    target: https://eprint.iacr.org/2013/382
    date: 2013
    author:
      -
        ins: Y. Dodis
        name: Yevgeniy Dodis
        org: Department of Computer Science, New York University
      -
        ins: T. Ristenpart
        name: Thomas Ristenpart
        org: Department of Computer Sciences, University of Wisconsin–Madison
      -
        ins: J. Steinberger
        name: John Steinberger
        org: Institute of Theoretical Computer Science, Tsinghua University
      -
        ins: S. Tessaro
        name: Stefano Tessaro
        org: CSAIL, Massachusetts Institute of Technology

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
instantiations of the scheme using widely-used and efficient
primitives, such as Elliptic Curve Diffie-Hellman key agreement,
HKDF, and SHA2.

--- middle

# Introduction

Encryption schemes that combine asymmetric and symmetric algorithms have been
specified and practiced since the early days of public-key cryptography, e.g.,
{{?RFC1113}}. Combining the two yields the key management advantages of asymmetric
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
{{SECG}}.  See {{MAEA10}} for a thorough comparison.  All of these existing
schemes have problems, e.g., because they rely on outdated primitives, lack
proofs of IND-CCA2 security, or fail to provide test vectors.

This document defines an HPKE scheme that provides a subset
of the functions provided by the collection of schemes above, but
specified with sufficient clarity that they can be interoperably
implemented. The HPKE construction defined herein is secure against (adaptive)
chosen ciphertext attacks (IND-CCA2 secure) under classical assumptions about
the underlying primitives {{HPKEAnalysis}}, {{ABHKLR20}}. A summary of
these analyses is in {{sec-properties}}.

# Requirements Notation

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT",
"SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and
"OPTIONAL" in this document are to be interpreted as described in
BCP14 {{!RFC2119}} {{!RFC8174}}  when, and only when, they appear in
all capitals, as shown here.

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
  - `Encap(pk)`: Randomized algorithm to generate an ephemeral,
    fixed-length symmetric key (the KEM shared secret) and
    a fixed-length encapsulation of that key that can be decapsulated
    by the holder of the private key corresponding to `pk`.
  - `Decap(enc, sk)`: Deterministic algorithm using the private key `sk`
    to recover the ephemeral symmetric key (the KEM shared secret) from
    its encapsulated representation `enc`. This function can raise an
    `DecapError` on decapsulation failure.
  - `AuthEncap(pkR, skS)` (optional): Same as `Encap()`, and the outputs
    encode an assurance that the KEM shared secret was generated by the
    holder of the private key `skS`.
  - `AuthDecap(skR, pkS)` (optional): Same as `Decap()`, and the recipient
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

- `SerializePrivateKey(sk)`: Produce a byte string of length `Nsk` encoding the private
  key `sk`
- `DeserializePrivateKey(enc)`: Parse a byte string of length `Nsk` to recover a
  private key. This function can raise a `DeserializeError` error upon `enc`
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
  labeled_info = concat(I2OSP(L, 2), "HPKE-06", suite_id, label, info)
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
  shared_secret = LabeledExpand(eae_prk, "shared_secret", kem_context, Nsecret)
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
`enc` and decrypt the ciphertexts.  All of the algorithms also take an
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

All of these cases follow the same basic two-step pattern:

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
information alongside a ciphertext from sender to receiver. Specification of
such a mechanism is left to the application. See {{message-encoding}} for more
details.

Note that some KEMs may not support `AuthEncap()` or `AuthDecap()`.
For such KEMs, only `mode_base` or `mode_psk` are supported. Future specifications
which define new KEMs MUST indicate whether or not these modes are supported.
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

def KeySchedule(mode, shared_secret, info, psk, psk_id):
  VerifyPSKInputs(mode, psk, psk_id)

  psk_id_hash = LabeledExtract("", "psk_id_hash", psk_id)
  info_hash = LabeledExtract("", "info_hash", info)
  key_schedule_context = concat(mode, psk_id_hash, info_hash)

  secret = LabeledExtract(shared_secret, "secret", psk)

  key = LabeledExpand(secret, "key", key_schedule_context, Nk)
  base_nonce = LabeledExpand(secret, "base_nonce", key_schedule_context, Nn)
  exporter_secret = LabeledExpand(secret, "exp", key_schedule_context, Nh)

  return Context(key, base_nonce, 0, exporter_secret)
~~~~~

See {{hpke-dem}} for a description of the `Context()` output.

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

The parameter `pkR` is a public key, and `enc` is a
serialized public key.

~~~~~
def SetupBaseS(pkR, info):
  shared_secret, enc = Encap(pkR)
  return enc, KeySchedule(mode_base, shared_secret, info, default_psk, default_psk_id)

def SetupBaseR(enc, skR, info):
  shared_secret = Decap(enc, skR)
  return KeySchedule(mode_base, shared_secret, info, default_psk, default_psk_id)
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
  return enc, KeySchedule(mode_psk, shared_secret, info, psk, psk_id)

def SetupPSKR(enc, skR, info, psk, psk_id):
  shared_secret = Decap(enc, skR)
  return KeySchedule(mode_psk, shared_secret, info, psk, psk_id)
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
public keys, and `enc` is a serialized public key.

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
  return enc, KeySchedule(mode_auth, shared_secret, info, default_psk, default_psk_id)

def SetupAuthR(enc, skR, info, pkS):
  shared_secret = AuthDecap(enc, skR, pkS)
  return KeySchedule(mode_auth, shared_secret, info, default_psk, default_psk_id)
~~~~~

### Authentication using both a PSK and an Asymmetric Key {#mode-auth-psk}

This mode is a straightforward combination of the PSK and
authenticated modes.  The PSK is passed through to the key schedule
as in the former, and as in the latter, we use the authenticated KEM
variants.

~~~~~
def SetupAuthPSKS(pkR, info, psk, psk_id, skS):
  shared_secret, enc = AuthEncap(pkR, skS)
  return enc, KeySchedule(mode_auth_psk, shared_secret, info, psk, psk_id)

def SetupAuthPSKR(enc, skR, info, psk, psk_id, pkS):
  shared_secret = AuthDecap(enc, skR, pkS)
  return KeySchedule(mode_auth_psk, shared_secret, info, psk, psk_id)
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
stateful. Each of the setup procedures above produces a context object
that stores the AEAD and Secret Export parameters. The AEAD parameters
consist of:

* The AEAD algorithm in use
* A secret `key`
* A base nonce `base_nonce`
* A sequence number (initially 0)

The Secret Export parameters consist of:

* The HPKE ciphersuite in use
* An `exporter_secret` used for the Secret Export interface; see {{hpke-export}}

All of these parameters except the AEAD sequence number are constant.
The sequence number is used to provide nonce uniqueness: The nonce used
for each encryption or decryption operation is the result of XORing
`base_nonce` with the current sequence number, encoded as a big-endian
integer of the same length as `base_nonce`.  Implementations MAY use a
sequence number that is shorter than the nonce length (padding on the left
with zero), but MUST raise an error if the sequence number overflows.

Encryption is unidirectional from sender to recipient. Each encryption
or decryption operation increments the sequence number for the context
in use.  The sender's context MUST NOT be used for decryption. Similarly,
the recipient's context MUST NOT be used for encryption. Higher-level
protocols re-using the HPKE key exchange for more general purposes can
derive separate keying material as needed using use the Export interface;
see {{hpke-export}} for more details.

It is up to the application to ensure that encryptions and
decryptions are done in the proper sequence, so that encryption
and decryption nonces align. If `Context.Seal()` or `Context.Open()` would cause
the `seq` field to overflow, then the implementation MUST fail with an error.
(In the pseudocode below, `Context.IncrementSeq()` fails with an error when `seq` overflows,
which causes `Context.Seal()` and `Context.Open()` to fail accordingly.) Note that
the internal `Seal()` and `Open()` calls inside correspond to the context's AEAD
algorithm.

~~~~~
def Context.ComputeNonce(seq):
  seq_bytes = I2OSP(seq, Nn)
  return xor(self.base_nonce, seq_bytes)

def Context.IncrementSeq():
  if self.seq >= (1 << (8*Nn)) - 1:
    raise NonceOverflowError
  self.seq += 1

def Context.Seal(aad, pt):
  ct = Seal(self.key, self.ComputeNonce(self.seq), aad, pt)
  self.IncrementSeq()
  return ct

def Context.Open(aad, ct):
  pt = Open(self.key, self.ComputeNonce(self.seq), aad, ct)
  if pt == OpenError:
    raise OpenError
  self.IncrementSeq()
  return pt
~~~~~

## Secret Export {#hpke-export}

HPKE provides an interface for exporting secrets from the encryption `Context`
using a variable-length PRF, similar to the TLS 1.3 exporter interface
(see {{?RFC8446}}, Section 7.5). This interface takes as input a context
string `exporter_context` and a desired length `L` in bytes, and produces
a secret derived from the internal exporter secret using the corresponding
KDF Expand function. For the KDFs defined in this specification, `L` has
a maximum value of `255*Nh`. Future specifications which define new KDFs
MUST specify a bound for `L`.

The `exporter_context` field has a maximum length that depends on the KDF
itself, on the definition of `LabeledExpand()`, and on the constant labels
used together with them. See {{kdf-input-length}} for precise limits on this length.

~~~~~
def Context.Export(exporter_context, L):
  return LabeledExpand(self.exporter_secret, "sec", exporter_context, L)
~~~~~

# Single-Shot APIs

## Encryption and Decryption {#single-shot-encryption}

In many cases, applications encrypt only a single message to a recipient's public key.
This section provides templates for HPKE APIs that implement stateless "single-shot" encryption
and decryption using APIs specified in {{hpke-kem}} and {{hpke-dem}}:

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
{{derive-key-pair}}, it is assumed that implementors of ECDH over these curves
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

To catch invalid keys early on, implementors of DHKEMs SHOULD check that
deserialized private keys are not equivalent to 0 (mod `order`), where `order`
is the order of the DH group. Note that property is trivially true for X25519
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
    bytes = LabeledExpand(dkp_prk, "candidate", I2OSP(counter, 1), Nsk)
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
max_size_hash_input - Nb - size_label_rfcXXXX - size_suite_id - size_input_label
~~~

The value for `exporter_context` which is an input to `LabeledExpand()`
was computed with the following expression:

~~~
max_size_hash_input - Nb - Nh - size_label_rfcXXXX - size_suite_id - size_input_label - 2 - 1
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
In the Base mode, the secrecy properties are only expected to
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
the receiver. Further, because HPKE uses AEAD schemes that are not key-committing,
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
  `Context.Open()` function in the same order they were generated by `Context.Seal()`
  provides a degree of replay protection within a stream of ciphertexts
  resulting from a given `Context`.  HPKE provides no other replay protection.

* Forward secrecy - HPKE ciphertexts are not forward-secure. In the Base and
  Auth modes, a given ciphertext can be decrypted if the recipient's public
  encryption key is compromised. In the PSK and AuthPSK modes, a given
  ciphertext can be decrypted if the recipient's public encryption key and the
  PSK are compromised.

* Hiding plaintext length - AEAD ciphertexts produced by HPKE do not
  hide the plaintext length. Applications requiring this level of
  privacy should use a suitable padding mechanism. See
  {{?I-D.ietf-tls-esni}} and {{?RFC8467}} for examples of protocol-specific
  padding policies.

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

All of these registries should be under a heading of "Hybrid Public Key
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
David Benjamin,
Benjamin Beurdouche,
Frank Denis,
Kevin Jacobs,
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
ikmE: 591c66abd531b9c8287cf76ac053efba38d61e994e7f656c30dab6723a8af9ce
pkEm: b6e788b2785b5db5e76a752f1a4a7b33e58bb7de3744289450c9254049824950
skEm: 683439661e9d9b3c71215a4a82b6821a54a21ddc97d5760e7ba461a56d64b760
ikmR: 8a219e9a42233826f165d2c1036399fa84cfb3bcb93872bc49287dfbe6f1fec9
pkRm: 693e421a7747f0b5cc05716351a9409de672d205f2a178ed70294c7afad22620
skRm: 480e958c0a0a03ab89cd09e2cb5a2232b30447df71b0288b96eb5d59cab13141
enc: b6e788b2785b5db5e76a752f1a4a7b33e58bb7de3744289450c9254049824950
shared_secret:
6817cec017ccc5a25d3a08e7d1fc75eba4b3698a9d827df743d3a243a95a982a
key_schedule_context: 00dd53f4a24da94754dd05f363191d063a9803d098415c2c82
eedfae1e5b44f897b78d74d1e5a553aec6506b75c00b4f71a132eedae22fbf04fb3b2795
48a3a2d4
secret: f71c9e9c65b2eb62ef3dc277865fa2fa837bd064105cfac6451b2df5e3751dc8
key: d9d566f12e8705d7f06f1db28dc83be4
base_nonce: 2b36540d322ad5964a6b9e6f
exporter_secret:
5d9fee94396e086981d8825a019bd6d5582f5d89d47158b2b0d64c26a44a18cc
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 2b36540d322ad5964a6b9e6f
ciphertext: 0bfac95d72da4a56168ca0ab8c025ba7f70520260cde4057ce2782007e84
eec9969294d1f2b323a3bf19186a3a

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 2b36540d322ad5964a6b9e6e
ciphertext: 8379e50a176e6afa3ad98ab03898aac824388e6e86f8e1c327485112ba40
7cd6e61414d18e2db7ddc559768920

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 2b36540d322ad5964a6b9e6d
ciphertext: 506bd1b0f7e980d648e4413f8ae06fdd4d25424f401a1984d266c85cfabf
5d9fba80c886e3510af88fb24408c5

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 2b36540d322ad5964a6b9e6b
ciphertext: daa13ffe8668d5e847d77896652495c7461df7fc014d8f80692d8789350e
d2760e531a4388336799ab7c9d0c40

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: f39542a6e45dc0e6225de671455fea9d918d4fa241c7fb301895a138ce7c2f52
pkEm: 25a22354b1b25393d4e6b11d36750a492ffd9bac7c074f5868d7ead5b6193e5e
skEm: f0d160a3eec4710d1f9308acc9ed44f6eff8a56b05120e334b0287c7888b786d
ikmR: 5aa0335739cb3dbafce48d5d9cccd7d499b0727b445522e1408aba8171aabfae
pkRm: d669cec49c19280cce80833dd810d7257023b40478d8186c88c96e80097c466f
skRm: 68f29eafb4c2455176bf0b5a710eb303b42b0575fbe38538cae7251ab773d953
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 25a22354b1b25393d4e6b11d36750a492ffd9bac7c074f5868d7ead5b6193e5e
shared_secret:
a4d169695feca7236c56dc07d2a3a43da83edb9a964ac23232b476e14cfb4d8e
key_schedule_context: 019091352b85603e6962c46b744ea932dc3817e8f943688182
965d3b6bcca57426b78d74d1e5a553aec6506b75c00b4f71a132eedae22fbf04fb3b2795
48a3a2d4
secret: 9bb26c08d2a8761b1ad5c696ea46db3c75e8fb63649af2290c87709610893cd2
key: 7905e373fde3715f5a57f0788b9d4bde
base_nonce: 3e9943b0d6714285524bef2e
exporter_secret:
85246513510459fc858b289d4f73c1ad7adab013485ed49066667be0e5e5626c
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 3e9943b0d6714285524bef2e
ciphertext: 03d1ccbf3f8366efdfdcbe10582cf6a62420674a09e2deafebfd4858c1a0
894ef7b823348096ce489d24749835

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 3e9943b0d6714285524bef2f
ciphertext: d0aa46849b996b760d15fb5663f647b42d16f04d9e3e3371585ca398ce4f
2e4a4176030ce03909d05d19a2d233

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 3e9943b0d6714285524bef2c
ciphertext: 42dc3035e77ad0f6cf67a03ea583e1e0598f686251f3899aece75aa0d32a
0ab404fe63214d33092d457ce08bc2

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 3e9943b0d6714285524bef2a
ciphertext: 408b1b7cad15df0cd776c625725ca6bd5940afea57bfe13cefadba741041
9039cd2a503ed1ebfe795e1920483e

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 0b119a7a132355f3c2a0ad03e10e252d7292fcde480e726d03a81f127d02c050
pkEm: ffb0bc4d8f0bd23360a7a533c12a4d0410b413da73d0876a1705d1b87487327c
skEm: 20484da5c6f5d8bafdedd689cf8898b76539a3c1db617d7395cdc4f4f2f9cc60
ikmR: 874ba77ded181cd1cb4f2b4f37386a5b2b86c84c57d2a6d1b93a05fb5edd69f0
pkRm: dd7a63455626e5c33a11cbf1e314c7a949b2fb833db635a47e9adcc25f19e829
skRm: 3835d6f979ea2181b97bd15388e2ac8897c1d1405bdbef24a6ab780290ebbd7c
ikmS: 2e369ba803dcee17dba926e4252b8dd9a47417a35bcf90f0e55e4af85c83153b
pkSm: 6aabf1e7b486cd13fdbde77e75ec7a23e15e965b86ef7ac3a91ea9c19f455c16
skSm: 58252076a99dab5f355a48af0d5db3561fb55b9a17d3e13ae512a6ccf8747a57
enc: ffb0bc4d8f0bd23360a7a533c12a4d0410b413da73d0876a1705d1b87487327c
shared_secret:
fdcad7684434cf118756c011c64b2544e71c82aff0175500010916279a7e304b
key_schedule_context: 02dd53f4a24da94754dd05f363191d063a9803d098415c2c82
eedfae1e5b44f897b78d74d1e5a553aec6506b75c00b4f71a132eedae22fbf04fb3b2795
48a3a2d4
secret: 8fb31816f23af1a01a3ce962f576f124128139a62930d7035f27be098d266aa6
key: 9773c94c6625c9a7ee59dab97fd25aa3
base_nonce: 21dcf14262d688b7af24bf69
exporter_secret:
2918046274554b8648f3aae9dd593a744fbbb1182fd2d05dde1655d7041d4600
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 21dcf14262d688b7af24bf69
ciphertext: 15f26bd792dd146838ff1ccb2a5f827a03c7d1c3c5dcc7c36e3afc0b6017
c51196df9c5a778af9ab3cd3896d0e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 21dcf14262d688b7af24bf68
ciphertext: f2af9f6193010212116bb316d9d96711d82f5cabc75171669fab74349a52
33d6c0855be62f528f2a9e08519ee0

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 21dcf14262d688b7af24bf6b
ciphertext: b0ac5fd0d0e0ec0039e844f6419f0b8db98bb9c04433fa76c25b93067f53
c8e13c3f153e3332ff73fb10d7576d

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 21dcf14262d688b7af24bf6d
ciphertext: 85644b5186bcb0b61083fa402ac7c91f7d6479a75db671bf2013944a3b9a
a9da9c704d87c0f093f000a91ef6bc

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 96360b18f7822f85f4a0a1dd200d00ab82ad0032b05a1f34cb120a0cbda4865a
pkEm: add99baa00e7555b74c6ce71aa930164573cd2b1d945af8762239e92a8cd693c
skEm: 20fe5b27f4d868fcaf9fa9d960cabe25d61efd034607e6cc3210f1f0534a7351
ikmR: 48710faa5c8b8b2a4447c9ccf1cc232fb49f6c0fd04b151949757e15b414eea8
pkRm: f0c5f00da33674d2cdb24cfaad4b9532d36a0004523b9760dfea6ddc56a8253e
skRm: 3834553e37a88c94799e3df9f053e8931e39f7033c12f257009303572558436b
ikmS: dd413f8d2d4b195a7cd0793453d04660203a51db65a57d16c2a720e6d44e526c
pkSm: 72a277e700bde918281817e6cf85424886f98220f89365069908e80892b8d30f
skSm: 08b90a0b40fb81f703e6435520586c7da06f2ef477a0378e60b38a4f456a0c7d
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: add99baa00e7555b74c6ce71aa930164573cd2b1d945af8762239e92a8cd693c
shared_secret:
94f5e6dec5754e69001e3a63647832c8403e75e21a94df1acf5f056c60d0b6a6
key_schedule_context: 039091352b85603e6962c46b744ea932dc3817e8f943688182
965d3b6bcca57426b78d74d1e5a553aec6506b75c00b4f71a132eedae22fbf04fb3b2795
48a3a2d4
secret: 6cf00e0589584b1bde61a63765571aeb9f3f0573d01f2e375d59f237cc7b1076
key: fd3320f848f64ee87a2aad0a68be16fb
base_nonce: 3674eb17633d9fefcc4be497
exporter_secret:
ded2df464152869d2a96f7c1f129341a5fb34d77c0fa0baafd9a5bc2c4ab6d6a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 3674eb17633d9fefcc4be497
ciphertext: 1ae6ea4b0b9ce236fb78828b529894b0a11ae66211dd09d121cf83bec8fb
d9b4a97071660cddad708fcf4720dd

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 3674eb17633d9fefcc4be496
ciphertext: 35340fbe3748e1edcd85e7d7c2a92ebfe12bf5a5f6ee2a71b9d4ad273bdd
d513e1c3dca6b98ad53445c30991da

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 3674eb17633d9fefcc4be495
ciphertext: 86c733b2eea61edfae798704de1a6747e822ee9ff9f1d2e8fff9dda02f0d
45f8cf752b78100fda00d03037cc58

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 3674eb17633d9fefcc4be493
ciphertext: 20622465f93bde3767af03ce76f6b17c00c83ce5f3c6672d60b5447a9c92
5ab73ebd5e28d4c741ba7cc0075e0a

~~~

## DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 171f5d09460ed3d1548c1091f2fad8f6e36deb3aac295b74b45bf50259c47e61
pkEm: 037a01fb15f146b69782d3c30a61dc4694de9e5dd9745bc72ee102ab6ee4c966
skEm: f8e47322a562c3cee3696ed61efd8875158ee5f52a81e9a5fbcdb9c72aa11068
ikmR: c560145a2ec58c3ea790bcfafa693968d27480a6349696574a99e076c8a4d33c
pkRm: 3a2ffb89d997a3e4f1599297790bf510690bb2d7634174da71780b2ea399604f
skRm: 10520858737ab92288e16b2bfe62263a6b3b0df57d771ed776359f7cbad4cd59
enc: 037a01fb15f146b69782d3c30a61dc4694de9e5dd9745bc72ee102ab6ee4c966
shared_secret:
4fff33b836fa6614e2c77937c8a3d3af0077fdcc9aee4cafbbc1fa532bd09086
key_schedule_context: 00baa0bb3cdf58aef2e3fd558b9def8ad7f7f902e7a6c83f25
64ca3e9eeb3d26f222e12f3643e2ad9a56477d7c83c86837ec8333a41879b3acfa67bcae
5d3201c2
secret: ecc6b6f848a2d9537671fa1a7497dced0881f2c5b9276cc045fd464b855c31fa
key: ebcce547b7a3a915838978ecc9dff85e6c9e05465a651d5aa277a13bc37cf7df
base_nonce: 0e9fd4c86bf09117672bd6a2
exporter_secret:
267fe045dc8bc12b984bd42fb64acef63f5049e6f1cace163506510896aa5386
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 0e9fd4c86bf09117672bd6a2
ciphertext: 8d58646d36804b70546d4b3e7ae257ffacf53b5b39616d16f980f28b9517
fec1da643665a890563682ef4eb523

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 0e9fd4c86bf09117672bd6a3
ciphertext: 88c1a6dc85ec79ffaa25237ad55a8cdc3684f55b1c5f126f55d9169736e3
194689768ae5e901408ad2a544639d

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 0e9fd4c86bf09117672bd6a0
ciphertext: 6d0bd0f37f6695d5a8471be81e343dcb99391eab3bf44b51662a1bcd7ac3
a2384d3c0e99171b99362ff0353e80

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 0e9fd4c86bf09117672bd6a6
ciphertext: 75f95dc409def5a6edef0813f750af2d512f7f8fe071bbfa360f5345ac68
f663e36eafedb297c37a830997572a

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 4065d076fa40dc4b9822f252dfd86aae5fbc6d8a978451fefe2c6adee0a3752a
pkEm: 9406902b7cd89994c943c2ecafb54624bb512d97e03e7a03805a0a7fa2189754
skEm: 30ac0eaae6bc2e74765536e8993a3cd9a54e1b236545bb5f36f7c7348f0ec678
ikmR: 40f8ddc363f09a96dea9ee4e476cf915441ca44476f081f78fc6ae987d6a9308
pkRm: 68487e0ef957249a8aed137964e214dbf8c1905e3b830764e386853fd95d8953
skRm: f81b84854e6f0698474230bcf27a2ebe1d57b2ffa946891de2674194b9a45269
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 9406902b7cd89994c943c2ecafb54624bb512d97e03e7a03805a0a7fa2189754
shared_secret:
173af1aa50980bd14e6fdb4defecc33cb085c5e6a29e11c86ebf082ccd7ea6fe
key_schedule_context: 018f4d1acd9ce69745cd8822fb9818aa352a419a838cac9822
6401609cc3a5adf122e12f3643e2ad9a56477d7c83c86837ec8333a41879b3acfa67bcae
5d3201c2
secret: c8a5d6f3734607c8d15db2714837aba5e31338ab4b862825f53d67f29552613f
key: 3dfa61a224f96c987e5b81a916389b5a2bdf3f5481443b86f187fad5f6b86cd8
base_nonce: 6a76370e2eece7c0c25e2ffb
exporter_secret:
593cb7bebe571c567078cf3f586ae7445944b2a632d9691da499522bfcb6bedb
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 6a76370e2eece7c0c25e2ffb
ciphertext: 837a5d0d63f409880162eab7152caea3c24667af4c0ca5a084dda82dde40
5ead37dc434be5ed62bdcb08cfdb5e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 6a76370e2eece7c0c25e2ffa
ciphertext: 909396541bd52a5954c3d5b64b0e7c3c4701f8253e8f0eaaffd231e08275
31da465a5456baaf84bb2be644385c

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 6a76370e2eece7c0c25e2ff9
ciphertext: 5d2c8d7240c712571a8c6edb5800c07d129f5439825c5ef169253d10eafe
3cc703b5995636c8b148bf82281067

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 6a76370e2eece7c0c25e2fff
ciphertext: 34ce9d082c1c4f30d1409f150764e0aee59d08667f838563acb6637dcd87
1964d07af70df9abd0c765e5bf337a

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: aa8f9c7b6e24761102a42a9f18685fe192eb69f3ebf8b65758c3bef42b822359
pkEm: 9a9c96b3d83c3de361c9461ae569bb31012e1e8e2ab81e522ce596f38a81ba29
skEm: 102f9b349cbb0c2dbb2cd42a25797e7a359e81710c0319013ff6b2e09e199865
ikmR: 6a00b42bcd534a6153319027dda70efd176eed620d999caafcd4f39beb6f1e87
pkRm: b46d13d85802d3c7fefd0c2a1f1e7939d668718a5d6ae78bac3abb00c1de4976
skRm: 80f80262917f46ba62b24bcc3a7463f94b7e45e12513ba00628450a7d6a21053
ikmS: c87864714467e330be58598d7f1ee9ab932d1688e79aaf6897e9a2584adc8fea
pkSm: b096d08110ca33b1fdfc35eafce2506753fe1da69ee4f763a2a1f9e8e96b875a
skSm: 482b16d27c88e1e9f0d2679e0a9b47f1525d6261e0f5c86a2c0f4cebc6a2f763
enc: 9a9c96b3d83c3de361c9461ae569bb31012e1e8e2ab81e522ce596f38a81ba29
shared_secret:
d3500faebbdbf5b74ae5779cb12c49d98e0c5db44c96f9716b016a9026b45e35
key_schedule_context: 02baa0bb3cdf58aef2e3fd558b9def8ad7f7f902e7a6c83f25
64ca3e9eeb3d26f222e12f3643e2ad9a56477d7c83c86837ec8333a41879b3acfa67bcae
5d3201c2
secret: 39abf4d90dfa1516e785efa7babfafb3257dd72905d87d60f9ce8335ce7e6765
key: b36936938c54d636d094bca5fc809ec8e7d591f6b762fb27baed8ef28ad48e85
base_nonce: 918645fde0a5293992a9c968
exporter_secret:
e70079046ea5ce127bd3b7437659f5e9b1d9f7e50adac01499c6901970a3757b
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 918645fde0a5293992a9c968
ciphertext: cb5b9eb59e6710d457cef2476f4ea6b82bf1b056a8dd9abda4698a614f13
4a1a744f2c8d3d9218edd46a9a8db3

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 918645fde0a5293992a9c969
ciphertext: c8fda3c71009031299ee9849456a70b5ba536bcc84ec315e91f8c46477b2
92f58b5e6a8c8879c7e7308b616a8b

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 918645fde0a5293992a9c96a
ciphertext: ff251753238eb6b15ac70350985859d57acd7b34cc67fdbc2cc59fa2f758
3675448a1ed51f2484510dcfaff3ca

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 918645fde0a5293992a9c96c
ciphertext: 488d1d7f782b242ccc56ab7d680e41bdd7438ec4736de9191886247d5d9b
b4708ee84aa870868a35a963596e2b

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 32
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: e35be6682528887e5a1f7d3acae9575c284aa5cd493d1bded9cb30c5a9a67f21
pkEm: 371145b2a0685a13591df34ce3c1f48165d5fe9962f20c4efa7fcbd53569ab4e
skEm: 801f3329585ae52515f1572fcf8a89cd3bad1d122544ab0c89f91d3f221a0f62
ikmR: 9bb89b210547e0bcb1e5f7dba91d6ed88840b14ef87927876d74c52021068dfd
pkRm: 6d14279ab914ab5ada05c829fc787617f52b4d58b6b6608b2c1d047c6e28686f
skRm: d0fdc040c9ba78ee7c63d948f30608af5f6f71100fcf6baa294056e41a04b472
ikmS: 9f499334a0533990c6fbeab4fd5e5c47ba2dbfdfe59cfcbf1241016f835700ae
pkSm: 84437eb7dc9839cbc958c95d0e2cab767023b2ed214d071ff2bcbe845c02a716
skSm: 90607143ab3ec8cd2c4bc7eb98dd4cad56e00e5b38c2148569d169914b61ce42
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 371145b2a0685a13591df34ce3c1f48165d5fe9962f20c4efa7fcbd53569ab4e
shared_secret:
0e62c9404892833322a864332e3588a093cfd220ba9453efd9724f88d370cf1b
key_schedule_context: 038f4d1acd9ce69745cd8822fb9818aa352a419a838cac9822
6401609cc3a5adf122e12f3643e2ad9a56477d7c83c86837ec8333a41879b3acfa67bcae
5d3201c2
secret: b5f2a31e43d9e62c6f6f9b207e0511cface0833369bb7f4af81c711dd56fc758
key: 16b29df75a13e4f34a11ddfbf4d20c75d66726cfa6c8a5e710ec723e622fd8e4
base_nonce: 2c1b8bc877af10aefa7417a4
exporter_secret:
f0322de06c632ecd6ab6152584e2cc82d9b07a8e8d53bf153fdbd62817226409
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 2c1b8bc877af10aefa7417a4
ciphertext: e30d73a6ce44a7a1868e2175e5c2da951119572e0b203b68e7e441ea0fcc
b78792e6e0fc12d145ec0c7db3078d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 2c1b8bc877af10aefa7417a5
ciphertext: 5967b1b673d705f7a2dadcac64f41313d0d9565332bf4937d6d2c6b9c87d
aef3ff4ed67190e02654f1ea890dd4

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 2c1b8bc877af10aefa7417a6
ciphertext: bb5f759c15700185b0767dd307580d418fa1761f99b9abc58b5d4065d6da
4697c6c6ff1f3456af61742d2cc27c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 2c1b8bc877af10aefa7417a0
ciphertext: 9fb9f4f3a21c53b8b0dcc9d68cbc2dbf8a4745dd7c87e7130c07a7b38fbd
de8f33c862df31d19c0f54a4ccd6e8

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 827f27da166dfeaa8929c92d2a67018a66d7b465a44c168220088d430461bb72
pkEm: 04a01b79a7807750c860610342450d54b5d4d91b8c51b698b37b6fdee6b97fa73d
a344ce28dafd89dc1daa929d1aa76349f6f4bc2bb0782674121a620072eb3b15
skEm: a679400e350e9da1bd1c36de49fc481cc6150e172d5f7aa9e97740b09f16f557
ikmR: 3c991968c9ce6f8e8f0fef41083ab91e9855b368b8714d78aacde3fc74b0fb5e
pkRm: 04a33be520167c96134a03754478b115880f307fcfc7ae9873d6449963e2487b3a
021be50200f71d4fe9c6dc4a2db04451fa8ff8b5840e1263697df8854b1187df
skRm: 31de13900c6f7ca8844239628949b07969cec1968fdc3307e5868d1ae10d7e2d
enc: 04a01b79a7807750c860610342450d54b5d4d91b8c51b698b37b6fdee6b97fa73da
344ce28dafd89dc1daa929d1aa76349f6f4bc2bb0782674121a620072eb3b15
shared_secret:
98ce9c4505de60f00baa68df92dfbcc89ccd1cf2bbfcbabb368a68b9e43b99be
key_schedule_context: 007a447b53a1bab6377f6d0fcd13c880e84b7b6f8c9d48909c
2681378f2dae2f735fb35e69f4b2ad8cb96fdecc61f90a4e3168e52786bc426eada7863d
a4b00f23
secret: 273a04827b269dd8f670ff33e60150bda39af36783b5e2c15e5973bbfc89e20d
key: 0f1d817716a9fcfb3a733d7a9495b5ea
base_nonce: 1b961630d98ed4bfde61a590
exporter_secret:
cec277f90ab42ff8b7e35a10802b5155f112eaf5b97ce19f9986ffccf77aa59e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 1b961630d98ed4bfde61a590
ciphertext: 6691e12b2ff62ee7afd44b1ffeb5cc90399f0509d153d8c1bd56dec39bc1
df84617a6daf3c1a96dcfa5d6eab5d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 1b961630d98ed4bfde61a591
ciphertext: 3bcc473facb1803c3b526b61e0cb5158ea0c9148df3a2b86b55e8e494647
20491fd557093f8303d825ead9b864

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 1b961630d98ed4bfde61a592
ciphertext: 32a45576443463950cca04906d2ca90d7271b6cab593a3a76bc5f19447ee
1890c1eb07c3b5419c6a2f3f480851

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 1b961630d98ed4bfde61a594
ciphertext: 03ac6b8b51f5a1897b59115d3b4854e1f044e25942c802531c1766db9552
f6262986eb089bbc171405b4c4cf7b

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 38ba9b0034b4b5817a48e331882952b5f73c3e8b3fa8bae22b1350bee31b0b52
pkEm: 04876ee0955ddb4c88a947b63910e9fd0cf6abd978c00f6a22470125364b82f61f
4d9d519f86521ef4122c30117650bb275ddb9a9b61d89aee117c63f51435de31
skEm: b9a314d8e61a93f4b93c7937bddb91ef36389ae09f10aa3aafe50723766f176e
ikmR: e4c2394942c47e25c24a93d4414bfa6c9ddc09c281f922a507acaa3276809f16
pkRm: 04c84a9e3179b21364316447674430bff4592844fcc1b508f3aded9d76bc324f6b
345c74c142e4d2d02c7c9ac3dfcab28f8a819bf105ea0bb917d4d1b4bf10a2da
skRm: 72ce45fe0b20006f839372528265f74e78dafb68f99e129f03c9f16d698005e4
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04876ee0955ddb4c88a947b63910e9fd0cf6abd978c00f6a22470125364b82f61f4
d9d519f86521ef4122c30117650bb275ddb9a9b61d89aee117c63f51435de31
shared_secret:
0bf5f8ce9a4b09a833ef37cee530074379950192aee7e1f349109509565357d7
key_schedule_context: 01fb64c721c330b25c0f399265499887256e6888b3316ace66
dd64c5d6b22282cc5fb35e69f4b2ad8cb96fdecc61f90a4e3168e52786bc426eada7863d
a4b00f23
secret: b51c63ae27995b77af27176d91babf25da5478ae3f7e299bc51a9ca6e8e61108
key: 3059b5cdb3be25ad8bcd5d670cfd8923
base_nonce: 5126130bfb1912ee174541d8
exporter_secret:
7f800f9dfbfdab3115997928daae8adc47849de64a329dca5808aad1eb88f9a6
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 5126130bfb1912ee174541d8
ciphertext: bb3993b1ef657c79a662487699a4ae4b50920422016e2f22f237c729be8b
189fbd2fdbd70dbcbd2da3ad5e80c6

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 5126130bfb1912ee174541d9
ciphertext: 0268d6531e9f48440822ab1e7b9584b63fd5d00e6943774f9766f7dff362
daa0755909cd722aa763bf2abcafb4

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 5126130bfb1912ee174541da
ciphertext: dd28d9ea055b12f32b1ad09ee917c3165fcc35ea83331ac0c79e8ad01938
54303ffdc7f3c174799cd1ee0c39f7

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 5126130bfb1912ee174541dc
ciphertext: 6186a02a8e2473fb290087c3356c9664cf53e0e6a41998f4f3a86d47416a
756a2cc8aec6bfbfebceafac88d7ea

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: b93d334f9b1de8d7e3ca0605fdb8d076a6a5fdaafde8eca7d67da75146413ff5
pkEm: 04d1c3e146ffd21b0798fb01db93a7d0b51b3e99a10a8794599693dba29626221d
548260d2cd01e74b9e73a4a26d1917e738f8d88b4086ee2c07a4ac25357de875
skEm: fb847e4b0f31996758312e37570ec8ba8c0eb4b0125ebd123fd77fab18f7972b
ikmR: f8a5c3a4afac029a42127f00ef607ef69c545eed537b7f0696e3d3a32dbd1b04
pkRm: 04fe92a2804e2a3881aed4a8460b91f17e473b31159f972a92dad286a43545f9c8
3a2c02624cbdcf16fa4a605224269cb59c2e60dd3e83b45c17e0716c824c7a2d
skRm: cd87881c87b05b913b482e18b4a6b4b4ce91c243b8e54cd66f36031ba9f0c197
ikmS: 972ef5a16a6c0d7f4a02d3411c7e15f962c90406820685627bfd1a30c26c92d7
pkSm: 043a47c673deb5133376a269eb24feca51148e34ad22dfbf62811b1851e0174f5c
65f0696268d4d9fb5e5acb616d669164e9658dd07de4ac7a811d6e076672f056
skSm: 17f1dcf868fae53516ebd9d4c20196ba3730db4f1ec9ff64914bf229a67b8393
enc: 04d1c3e146ffd21b0798fb01db93a7d0b51b3e99a10a8794599693dba29626221d5
48260d2cd01e74b9e73a4a26d1917e738f8d88b4086ee2c07a4ac25357de875
shared_secret:
0c3fd84ee365b91ad3df60c287d76603f3aec351fbb1d6e33325654cf4557b5e
key_schedule_context: 027a447b53a1bab6377f6d0fcd13c880e84b7b6f8c9d48909c
2681378f2dae2f735fb35e69f4b2ad8cb96fdecc61f90a4e3168e52786bc426eada7863d
a4b00f23
secret: 61498735aa7a83ed2aef880e240314a1f793d6e847f588b146bd6023e5701de0
key: b3bd2473b024dc462f0599ff8f88f26d
base_nonce: 5c0a4779fc33b33cca08f223
exporter_secret:
12b1f1e6712be78f1a39320356e81ff8dc21ec457c35e4d98aa08af0cc6ee717
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 5c0a4779fc33b33cca08f223
ciphertext: 5d19ca11d7fdc8693ce9ca04832507c912894b0ca156b620fe40e56d4f35
92977ae52cda9b5dfaf7ee348ec0d6

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 5c0a4779fc33b33cca08f222
ciphertext: b5a0b849efbf88e71fa44436cd3b4635bb15de2344e63946ce57daa891e7
475e1f510212939aec220e0a547326

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 5c0a4779fc33b33cca08f221
ciphertext: 450eb2c219c2df213346bb814e2e46f7e1741a8851d26a590080ac08138b
cab203ceed3b1be762a206fbd335d3

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 5c0a4779fc33b33cca08f227
ciphertext: 2143af9290b40fb86537ebb8a7e5bc63548de87396775c0cce707cddc722
ff44e155854d452a808a027f35c269

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: ab72de85d4f56ece8c99eaf846f1309761726aebdfcc98ee0b2325a0b0e05747
pkEm: 0451c17475f92a0f950a56bf5912798fd7a45ba0048fa04302c2c8013692f31916
5da9d853a2ecd8399d323e0a4d8fbb24c22031442709129c73d9e38194ee19b4
skEm: 55d949c902bb9d9e7a76492bf2f7cd90a1f6414e5d7bcd3d4233f9a9dd2e3d9d
ikmR: b27e63ef5f94a3aed99170485f0c9335b160c8cd56c3b270c11442b0d66cb458
pkRm: 0415df4b0cffe5238d4e5d9a128fd19ef0b1ca9c3a499e250060e4fe186400a8d6
8f5e16fa0ca3635c411e0fb0d7059757b5612d3803c69f96c1c140fe80fa5282
skRm: 8d6c16c0726453a3d8fd5136e9ffe1dc4760efc53ca4d8b5adbcfa496c073223
ikmS: 50750d36da3239c76d4d4ec1129460e5fec239b77d7a0de8094d58da7d4a24eb
pkSm: 046f215a93873508bbe37be23394cc79478fe719b72f4faca3237d67532279c74c
9f1fd2b69a82bbb92af5b3b3af50020d7a199ed7e8c617aee8c78d5f3fdb15bd
skSm: 1ca55b7f8393abf475b1283d68bbae5daac575702da3ecbbd0485902ac93dd30
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0451c17475f92a0f950a56bf5912798fd7a45ba0048fa04302c2c8013692f319165
da9d853a2ecd8399d323e0a4d8fbb24c22031442709129c73d9e38194ee19b4
shared_secret:
d5e50b21898311eb7d7cb91e84f08232a105d8cae469ab99a29b8316866762d5
key_schedule_context: 03fb64c721c330b25c0f399265499887256e6888b3316ace66
dd64c5d6b22282cc5fb35e69f4b2ad8cb96fdecc61f90a4e3168e52786bc426eada7863d
a4b00f23
secret: 14af946a81d6e837c1c99892a9fa2f5c829a731f56288c80e88725fbe10da1a6
key: 78a83144b32ef6a55d8e95b6cf608a69
base_nonce: b025809b6d6be90692610c2f
exporter_secret:
4aab5e9c447f32892d0f171dd168b257e0b827da0fcd53543cd1f47649762220
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: b025809b6d6be90692610c2f
ciphertext: 6783ff2f2aadf3bf9b98292323023a5567cc40567b8a209503a5b5968fec
bd64f47d41e5c2737bc53d2dddc51f

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: b025809b6d6be90692610c2e
ciphertext: f907d0e114baf7b49b6e8098eebcf6f3647fcd2760028075eb58d1152db8
824697092bccc2bf4a3b4cda287b19

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: b025809b6d6be90692610c2d
ciphertext: 4fc4a6529045bb7be5bcf7b4e5c56be58dbceae2f7435063388d9cca800e
6329b2182ad2a37fe3cbeaa69519b6

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: b025809b6d6be90692610c2b
ciphertext: e17b1941d52b323912a577da1663a441c0e9a82a8e3333487f85787e3e5b
9cdbfc819a2942f54332fa80d377c6

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA512, AES-128-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 6a15ae6050f8f3a0aae56777f77633e81181c03f218a212691d3560a455cc5a8
pkEm: 047a1779b86e30662292221d847731c01bc152f1c3ca9816233ca43b78d9d37b1b
286e8cb0fdd6b56e5feed4643937b8054390c70c17e7db87bb5b9fd39bc3ddc1
skEm: 243c0710bfe0505bda854a3e59845c057cef975868313cac1870b7ffa5b50ab6
ikmR: 4aabd6f3276cf14e0ba493e8937306019f2af84b6c079b7cf89a81a4539d0039
pkRm: 04410fa2c036febbe2b60303b4d1eddf24ae346a1ee13fa1c40b73a05f223ee1d3
66329798d7c53d2a25662976d05742effb776df47ebc1333d36a9d3b71f35097
skRm: 70662f22846232d0133a10997d4d83310b4fd4adeca6073dc623b98855a1592e
enc: 047a1779b86e30662292221d847731c01bc152f1c3ca9816233ca43b78d9d37b1b2
86e8cb0fdd6b56e5feed4643937b8054390c70c17e7db87bb5b9fd39bc3ddc1
shared_secret:
c942447bed1dc6ab95b4e140fef92a9388915f55243af081f2a352f79b308f16
key_schedule_context: 00f86054b6a97a160a8eabaf21ac0186ad4fea8e6eb33c984f
efc264eb8f098c90368daa9c96dcc998d12330b913f6c4cdd54cec86cc624a9e8aaf94dd
3bb351b066e461a725080580fc1de13a535af76baea621a8f452cf0e9a638f1011105114
b4db515d224bada4a152dbaad88a1594e11564230c6795a333b19a32d9b5cdef
secret: d7644fbf9daf4a0f1c02c814225ab1c290b4cf4a8e40c03b873bf910060abe63
2647f4b2ae684b325a93bec27a1f36866963d94b1122d1a8dc819cedae28a20c
key: 29ca2d66bbfc6736ace0b1cc015a7669
base_nonce: e34dc7cdc34e655018ee3fca
exporter_secret: 4173b69a1acf63bd5707d66e6252662ae69bd35ba66af3bd2e8e418
2d74b81c54267db3a638020aa92734a5cb4ee654c1d39f99625b9ac2299bc0dfab64902b
8
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: e34dc7cdc34e655018ee3fca
ciphertext: c97691cd3eb5460c7b401327338c51a27607e10dd27943d00e4259c248dc
becf08353d0b07fd00786c33efd3d1

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: e34dc7cdc34e655018ee3fcb
ciphertext: 198266abe509e12c2a47b08bfc90de09d7da4d1566138ff654867e521197
1765e5d7bcf65ae220471abb40903f

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: e34dc7cdc34e655018ee3fc8
ciphertext: 08316cbbaba99533fbffcc287ff0ff2ed1359765f07c49eddb06c29630f3
24cfba6c3b4326f7988c3cd7914e05

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: e34dc7cdc34e655018ee3fce
ciphertext: 8a2adb299ecec60cbe46540ad84638b60cf2d5353634455e89c9d1e75c88
088b7201d042cb34a18bc1e9a55e52

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: e76eb1beff6bfda05df316cdfdd206984a5647ed4ed66ea74ce66626a115418d
pkEm: 040eed8074afcc38eba0057f3d3c87dd3cb10fc0aa1e80a19cf2b5e4e65da68d1b
6f1d447e5ad4feee1a1a50bdce77c8ff76ce6706db8e798f7aa88856f919d2fb
skEm: c3662b4f5edc906af1e2fdb243d26044b73a33199b3868ecc0be3384ba49b9d1
ikmR: 883e9d3390eaff9fb8fae73953fab565498fd327a6592459763f97b5e50c1516
pkRm: 04f80d0e92e33606bedc68e4b52b2c67661029b3b191f6bb338a7ea533082c8dd7
e4f5bc26876f471759053a5fc34e72e2e9cfff32e053bd056576f4782f7f86c5
skRm: f6d6f2516816708b086b42cf3ce12a693f7abfabb090119be8f93c081dd1e40d
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 040eed8074afcc38eba0057f3d3c87dd3cb10fc0aa1e80a19cf2b5e4e65da68d1b6
f1d447e5ad4feee1a1a50bdce77c8ff76ce6706db8e798f7aa88856f919d2fb
shared_secret:
3b2c0130c6baa380542b728f576bb8da2850f5529be40d0927be648fac9dcf56
key_schedule_context: 0175285841348a413918874e96b9703074fa763f2bee449918
c13b5bb660b8d21636f88958e593fc9b64692dd669510ca2c96a893e74eef89592b98ccf
fe182e7466e461a725080580fc1de13a535af76baea621a8f452cf0e9a638f1011105114
b4db515d224bada4a152dbaad88a1594e11564230c6795a333b19a32d9b5cdef
secret: 7c0b9aa5173a0d8a9bda91bf7c212cafa73dc47621d1e18a6ada21c9c3307f32
8d3b288802ae9c3d145af13a6587e5045c35c7a8d5c9328900176abcc2bb3df6
key: 0fe5fad216ec3cfac88273d43e537b45
base_nonce: d8bc3ea080233a9700f039cc
exporter_secret: 081e617c3369139d11873a934d7686f029f940e62ff9f6828bfce60
0dae5023e474a32b9fd0c6b0fc2ec11b34cd18d7465ee8a12278a66f953b708618103960
a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: d8bc3ea080233a9700f039cc
ciphertext: ee640088fefb77872f64a161f798a592ca180f48f10b181f0ca2294aa7dd
db5be141a386f3bb3c13fedcb18957

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: d8bc3ea080233a9700f039cd
ciphertext: f6e268d392edf8185e455b8eaf0874165c27493ad07cd40b54a7a14d2b3d
ba3e763e7dd377ab2aba444c5f0958

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: d8bc3ea080233a9700f039ce
ciphertext: fcc7800b1c68663af3043e8a4a3876b0197f9dd1816d8fb385ded0d39ca0
65a9a2970a7f6879583b784784d29f

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: d8bc3ea080233a9700f039c8
ciphertext: 244506a7408acfa8afbdd3f3c95c7bfa6cc64948cddfa510e0c18a04caac
a4b062f7eba992865cecae15623e4b

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: a2854b15706ff6b1c184d1134545cd7496d6633ad1bb6bf3b6bfc483be5856b6
pkEm: 04f87bc02d64743b79d6e2c5bd09d9e7ae23dd6ca38889e67977169844e0e34968
6af974bad7f23dbeb45c9c4b2252bb49d02152e9a1ea5508ec313b38c02a7bbb
skEm: cb85703053a329c978e1cb9fbaa1d7c9251e0adfc176093a6f4296d45c92ab27
ikmR: 4a59c85945993002cd16ef7ad651e46018e0db28844a6aef4f3828355b389828
pkRm: 0416358ac8e863e83c4690c690b0bb3ae1dea320446ec1c18badace8882cc08340
50ecfe6ba5da1b6bbc63b47364ebc95108f0412c2c6864f45b9aca4bf3cc28e0
skRm: deffac20a610dd2d1be848f01c6f6303ad9db43f220f331b3dc6bd52411aaa9d
ikmS: a06672f3c860ca33c54e0f8b503ec2e7442fad9cb190c58c9dfa14fd07de3edf
pkSm: 0413abf048f0e39718dd2fd36213596126c905cc0c239ac6847bf3a3b03409993b
c75dcb77c1a1778b8c6570b1a244b4d3f6fb848ceb4d054b7377a69264fccc29
skSm: c21a9dfd394b1a9b4ec3510163245548a3a2ed15c8e6cd6e0d9d39afae8e680b
enc: 04f87bc02d64743b79d6e2c5bd09d9e7ae23dd6ca38889e67977169844e0e349686
af974bad7f23dbeb45c9c4b2252bb49d02152e9a1ea5508ec313b38c02a7bbb
shared_secret:
912178dc1b35e3779a35a5ebdc307f977f999ce9b644d6902586b2857f813169
key_schedule_context: 02f86054b6a97a160a8eabaf21ac0186ad4fea8e6eb33c984f
efc264eb8f098c90368daa9c96dcc998d12330b913f6c4cdd54cec86cc624a9e8aaf94dd
3bb351b066e461a725080580fc1de13a535af76baea621a8f452cf0e9a638f1011105114
b4db515d224bada4a152dbaad88a1594e11564230c6795a333b19a32d9b5cdef
secret: 3a0745583458a11a2c3ae203f991ca7b1fb5119f9736cbb88ffda692d841bf89
77a3cc206582f8554cb971b7a37cda3c3f20f034ebac87e7b7d880aec314423c
key: 0f77225c162f9f56288288af3d59f136
base_nonce: 9b668946816a1d0d6c9d7e0a
exporter_secret: 27a55255900f52b16c21d3d30b5af4e72e12c6d798f450067c31252
eb7c53e22e5013cbe9b5fe00f559ff0f8410c53c7e8094732637f7ae350da39ee9043824
e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 9b668946816a1d0d6c9d7e0a
ciphertext: e66b7307b8716dc8c140ee07301da61f27b3cc2004c732c43de4871d337f
e47e5b5275e8f60af24e4b2cb55cb6

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 9b668946816a1d0d6c9d7e0b
ciphertext: 3a2009b612a080e6d0debf621a2a0a9552843d9d09387854481a9bb656ad
6eab30662051c308e4339f8fe3ed66

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 9b668946816a1d0d6c9d7e08
ciphertext: 9334ca5ecf7f8fa1e405a562b8615a74789592af762ecbe7d0aa68ad68af
a43e39e6d4ccc5836d13259d5e90d1

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 9b668946816a1d0d6c9d7e0e
ciphertext: 97ba304c7d53dd535b0e0f3874792a0a8d75e3d3858244b965f304ba0e35
c1bf190e0475bc284d47e045796bc6

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 3
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 6145eeffb6f33b85f251e569175ec958a2df0bada63280e84021b3693b6bec6e
pkEm: 0450a79483be0a777de1d5d6ca60d2a32b351ff99061d360e433ccd023b71640ff
6dd6b40de4b30634cdb22e804d12b0082c22dbba47ca4775cdbceaa78dcef3cb
skEm: 734193928a6d7dd9519f6bc1d6028ec480557e001e9cc0dd7b543bff590e7520
ikmR: 66b2e8f713bdaefae23d0bd3bcf5ac7567873d399cfc5821928e008f981be915
pkRm: 04de9e529271229501a424c3784b40aea872ad36d7b05bf5dbb76851349eadac3f
97a729b1f697f154d3e0a5a53da3ff6bc59fcb6bb543873962fda2b08238ded0
skRm: f60d52bfd936a8aed2fa5790e503bb7f8326537defe8d20978271fdb489d0349
ikmS: 247bfb9453018e7456d0fcea197bfa180f8ed21fb03c50781d4d1ea76c73b41d
pkSm: 04e8e975005ffc567698b3d6d48bf967c7306d5a480ac049589da8bda889235442
8cf88a4ac3188901b976805f34a2b9e250cf1ae0da92ba5c35cc7cdbdabeda37
skSm: 601430726eba46116c821300a638919f5404f30abbe289f08e63e164993ddcc4
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0450a79483be0a777de1d5d6ca60d2a32b351ff99061d360e433ccd023b71640ff6
dd6b40de4b30634cdb22e804d12b0082c22dbba47ca4775cdbceaa78dcef3cb
shared_secret:
d4fdfb21883e4ae355689f48e8fbc526e5ea54faae5e339cdd951e391f6852a0
key_schedule_context: 0375285841348a413918874e96b9703074fa763f2bee449918
c13b5bb660b8d21636f88958e593fc9b64692dd669510ca2c96a893e74eef89592b98ccf
fe182e7466e461a725080580fc1de13a535af76baea621a8f452cf0e9a638f1011105114
b4db515d224bada4a152dbaad88a1594e11564230c6795a333b19a32d9b5cdef
secret: 300eece0bb0cb0d39acbaa2d513f918325ed684e8f79213e0f961122d84c2011
20b401fcc8cc1a2f125032b9eacb9939edd1307883dd8b567815108341903932
key: f54a5adc57021b3d66c2687cc3b82fbf
base_nonce: eae87fad2b6a87f488bad689
exporter_secret: 2b8756aab46ffc1b45ebcd31bb555929cea5996181bb0d5a5426cff
af77031923db93501ceae9afedaf800cc3433650654b589634b144cddab69dbbba758f53
6
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: eae87fad2b6a87f488bad689
ciphertext: e38dcda1e88fa449b239ff6121a536a7a426e3913a06f0db3045d1f4a9d7
40dd14df928ac643be70cfb6865c37

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: eae87fad2b6a87f488bad688
ciphertext: 8e3dc8f66d5cb3046355971df7bba3ce2ca34b31d468a36054f5ecf359b2
1c044f56d50932187ccc88b1b94802

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: eae87fad2b6a87f488bad68b
ciphertext: 5ebb15688bca07a50c773d52baa5a4ce37a72c22fe472b36fabb8195bc29
a2e96b2f9b4eb0df7a457c258b0551

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: eae87fad2b6a87f488bad68d
ciphertext: 0092f075eecc4088f1ae429d980d5270c28a38447f6a66b66c7d32527e8c
2bb7b9a31049d9a8cbefbd4ace256d

~~~

## DHKEM(P-256, HKDF-SHA256), HKDF-SHA256, ChaCha20Poly1305

### Base Setup Information
~~~
mode: 0
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 9df8b42914e9fce352d49c922ddf1fdcd48f81a956ab5acd5ccfbca35f5c0beb
pkEm: 04b8c41a294b8d1da8bd64a9894abb3d579904b86f3aa4da89f4e9563189d93ce8
110c51b3b38ef23b8b9296a596c71ab48947b97d65e4ad545bb4def204ef5c88
skEm: e8b7bae455be2474a579d61eb0d012d0c548c6992a9cdced6c07c503e8fc814f
ikmR: 211e281360f0cdb9c2b5f657619628a0e2e9ef6b246949f165f5ee950f9bc7f8
pkRm: 04b8562b9b63e1ee70c11043c660b1a274a3cfe6c79ab2d53a2f3b416534a0f084
0261ef7e883b80b1a89457de1d98dbcbfde581a1c0536393e387a193e231c6dc
skRm: 7e3f0513ccf1a4b367262b0422472eb3b7675ba6f90d9e14e1f0cea9bb27762b
enc: 04b8c41a294b8d1da8bd64a9894abb3d579904b86f3aa4da89f4e9563189d93ce81
10c51b3b38ef23b8b9296a596c71ab48947b97d65e4ad545bb4def204ef5c88
shared_secret:
e820e9b5996be00574b297c31f211463df6448a5211f62e5949ee149a8a537a6
key_schedule_context: 00712f80079bf04cb297132973d915af2772f9861f8d6324ae
66125ba4ef6ab7e3136812e221b08af3c969408f8cdcda2ce9d7868aad8ef22f6cc26232
c25f331f
secret: 984ea0de48e81f4abab7f991267adba1f23174812d7c224e40f2971e2da5471f
key: e9a081bdfe019f452e5799c23351a83c7fcde509d5a3859a3557c2ffbc1fe191
base_nonce: 29636484614bd5b3f34ae257
exporter_secret:
a6fa6f2f65d731f4256386ffe35ea3c42596c48ee8c77e4f593f1d417469dda8
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 29636484614bd5b3f34ae257
ciphertext: e6d15f7ec405370ace66b7a69c4caa5d662f800b786bff050c5bf0de57be
c09375161f02ba9b5bfddd6d91e64d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 29636484614bd5b3f34ae256
ciphertext: 69d3716e0a87a05bb09bebee8074301f2d689cf26a6f6937f3ec67222456
a172eff815edf3d7824ba90d3c7143

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 29636484614bd5b3f34ae255
ciphertext: 0facafca02cd1f9d07a3b8e12c5e2971b6b602eca85286a6af34c65e34cc
4a219c6c26a7dc80aa5e5ee47995cb

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 29636484614bd5b3f34ae253
ciphertext: e50bec54ad67e827fd866c86eabe36e63692bbbfb26fbc597acfc38874e9
fb1ce6c7c15189376881cb5955cabb

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 7d4bdde35e62157602b7f6647fcc5908d4c7aa568f19d26d3c7e0e6cd1c7f952
pkEm: 0418f0e825f34a05b5b5fa61bb99e2b50b9f3437bcb330e7008e80885b80d918e6
89556d104b18ea186e324044dc3a2012a36ceb6e63d3a4b2db68b8301cea3469
skEm: b55f711a89c4bf35f12a5cc36d3220ad571a928368213e07cd9875adecc56d80
ikmR: 4d8a4eacc6b0fb10dc3ba6a94057caa236f2a85f21dc8c613ff8f01fd8ac4e04
pkRm: 04807b48c94311e802aa56f7b00ae88c0b9a6ec0fc948afcd5bc6e5e0ad41aeb4e
9ef2511bb9a6b7b9e0522dd5868cdb40cc773f030ac2751cfd745cf9baa51357
skRm: 273c67b47a735b25d1bb765f138522bf3cdc6a64f3d39b968e84f2475418b65d
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0418f0e825f34a05b5b5fa61bb99e2b50b9f3437bcb330e7008e80885b80d918e68
9556d104b18ea186e324044dc3a2012a36ceb6e63d3a4b2db68b8301cea3469
shared_secret:
6b78677651bececd4e16e50636826de091164be7aee6704f11e7a864ccea85d7
key_schedule_context: 014676a8bd153b28d8133100b9fcdb79438c549578bda55d61
d9d3fbb4747aa127136812e221b08af3c969408f8cdcda2ce9d7868aad8ef22f6cc26232
c25f331f
secret: 12364d5dfe5af7f4bda8ec485163890911408babf0143f151cffce1b27503980
key: 62f430439c16fe9cebf9a70cbdac465531fb9cb81e55d21f7034620457e75257
base_nonce: a387d84007bcf32f061ed0fe
exporter_secret:
1642a15dc9da12df5dde65486b3e6215f3c62db433e44b10237ef1c0452c036d
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: a387d84007bcf32f061ed0fe
ciphertext: 7081dcf888fd5f5f206d663add83bdb12e0d07613dbc2f0bdf25469ba7c5
9955200a88df18f5bb4730b44387c7

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: a387d84007bcf32f061ed0ff
ciphertext: 1689656b247e694c9149f0ade93273e4c5b2820d8d62f6407624de54f259
07053bcda60a0c94e843fd8c8e6362

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: a387d84007bcf32f061ed0fc
ciphertext: 3298ab5522a3630daf242803e95992e7f3e1afa39ac28492351912c9cdac
3e31fdc8f2aa9aa017384fe10877c6

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: a387d84007bcf32f061ed0fa
ciphertext: 733d60bf27e61c298099aafbc0f1c9bbef08fc5ad7ba06d573a7e4ee6d17
6569efa287858bce4beed1d8504239

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: d1eb88204fbb88b34b9bfd437ed0a3385676cf13e1d16885d26a9271ba9c9100
pkEm: 045626e00728b69683a548289c4ed133d5dbe70f1c9386867c136eafbce30c577c
5be756f768179a75572dc45ab5ff282e0b5d134a926933587e0dee813c06afba
skEm: 47bb319cf209f0c654fd0f8bd4115201681695df00730d11b521977d8efa8c1e
ikmR: 3c9d1ecb8e237ed1ff9338b1137112de3e0ff4e27b4874510e7e74ca4dd92daa
pkRm: 044aefaf297802c7d01062f1a2ff6648035fa70b0b4a9c77f15ef8a6fd9ce987e0
3389c6df8e84ba367cdf0746441286976adf7b49dccd4f25b5adca1d0b256b26
skRm: 6db9c6bc53ac0d62ef958dd40e9af16b202d3d91c238a5e356a4c5e0d327572d
ikmS: 11d4a3df0386a92456d5b16b49e5b74ae674c7b381925762d7a180d3b0fa8df7
pkSm: 0485bd9c999fc20de57ee036f030eca455e2f5d5dbd9271acd500cc675851fa663
e464d02bc47d45ab4656365961eff49dd8c0fd5704324db28fd3e74c761317a0
skSm: 02842413302245517bbb6fae9797092b394b4cabe618a2d1d6c06e67b856d26f
enc: 045626e00728b69683a548289c4ed133d5dbe70f1c9386867c136eafbce30c577c5
be756f768179a75572dc45ab5ff282e0b5d134a926933587e0dee813c06afba
shared_secret:
067f63ce4c4f4746ca0281b7c04fce946da9e070ccefc475d0274a59d169f2f7
key_schedule_context: 02712f80079bf04cb297132973d915af2772f9861f8d6324ae
66125ba4ef6ab7e3136812e221b08af3c969408f8cdcda2ce9d7868aad8ef22f6cc26232
c25f331f
secret: 06e4427df9b7ebc39eb5fe85913ab4130d0a9b1a38ec47c2f91a03507b0fc163
key: e3c3372fe9188723349c2fdd611266291a808b31fcb07bc858f8fbdfdce63cf0
base_nonce: 93f581802e7d3f752e0736f4
exporter_secret:
dfa30f8d46590cb9f706999ece2e76985203e2eeeaef2ac56b1bef05ace34fbb
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 93f581802e7d3f752e0736f4
ciphertext: b36268d0ec687407ff0539e45e1877ae61da0f254c79c14c528b69c587f5
4eedc0739febf28f48d32a822c383c

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 93f581802e7d3f752e0736f5
ciphertext: dbddea82e7da8d040fc1ac2159f55efe7dcf8b173f132055a5990073d801
dabba2971af701cf0d7fee191c7f58

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 93f581802e7d3f752e0736f6
ciphertext: af424c3453b94e5c8107d5d499d494aaa765d0184b05a6f55fe2496cf153
5d87325fb20ad705a9ac1c476a1370

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 93f581802e7d3f752e0736f0
ciphertext: bc08acb8f1a6f75e439f0689d03ac878c0eba2b56799f3fa19b7eeb39ef0
87b8baf4e0da1d854e84f66080a02b

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 16
kdf_id: 1
aead_id: 3
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 75422f8364da556a73f8ff16f70ab9b46b9b89089baf7c6897dcd3f040713d57
pkEm: 0413a0da6df148265544f31c634c67f3e12c323dfbc07b2d652159242371e04314
1f323958c852bc10646ca44a4e641b162432aa4193b6b8b93c06d11831568481
skEm: bd91320fd96616044246944d486f03bb44c5b2d46d587cf765654098d73cad38
ikmR: e1b8fed84588b7ecc6bab2dccf2a93508075265de18856b9f0768a3dc1b3fc2b
pkRm: 047ce9f6d438178cd79004a762d794657893fdfac7d66874688763a35299463337
bf85323da8672c3ee276b762e63853a7f3a8a6bc1b07b3a8b0edf804499c94e4
skRm: 1164c40d571ddd9a7492e903a1b0eab01c5d21233d4f0ed6ea2c0f477139a110
ikmS: 557e7fe9f5bcab34814bdc82f61502bbd35fa81595dd610f553bebe032412c93
pkSm: 04363e618990bde7ac3f127dd38289eb9efcc0af2630bcb26f064fc9c9a52686e8
f2b2adc515b26360f15d7d41f552b1ae5635ab4db5ec4aadc5243e250f1e748a
skSm: 46156d3143e7de7866b7bb6aaa098afcac3c14d179dccc77af48ed5d00f9f8be
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0413a0da6df148265544f31c634c67f3e12c323dfbc07b2d652159242371e043141
f323958c852bc10646ca44a4e641b162432aa4193b6b8b93c06d11831568481
shared_secret:
80a227197d8a4c87cc7db3bf2d2cce3b37c94d6a2c9222cf442209794df68ee7
key_schedule_context: 034676a8bd153b28d8133100b9fcdb79438c549578bda55d61
d9d3fbb4747aa127136812e221b08af3c969408f8cdcda2ce9d7868aad8ef22f6cc26232
c25f331f
secret: 98aa5ee99d2738c9bff2023f45f8a279be57180fccfe7fa8f820ed32464bb011
key: a0464ab1cb323356b3945c8c90afe6985b1e7eacd36292726edce5d96e17ac33
base_nonce: 8d4cd26358f105692d0ae29e
exporter_secret:
63343a898ef5717a6a127b9c64a80f1068376d6c65e6b7108f87f5804aa6c945
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 8d4cd26358f105692d0ae29e
ciphertext: 043118c110de11697966d1d4fb3782d4d5043c283b4fd16e4630656854fc
2cff45b0f10ce205914f79771b039f

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 8d4cd26358f105692d0ae29f
ciphertext: cfc4100ee22cffd749d01f95483a97d5671170732c36b1e7232c016566e9
349c744dd50345eeeaa57d956a2fa2

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 8d4cd26358f105692d0ae29c
ciphertext: 0cf651270751e720ac78f8d995f1a5ec96e6dc107f77a4750e484e0e2e6e
b1f7c3da4f018e3486752409389ffc

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 8d4cd26358f105692d0ae29a
ciphertext: ffbb22b9ad07e95b07b34eb07a5f82ccca90d43c3aa89ee5a23a66cf34d0
3b835a7da410505c678fe6e617c3ed

~~~

## DHKEM(P-521, HKDF-SHA512), HKDF-SHA512, AES-256-GCM

### Base Setup Information
~~~
mode: 0
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 3fdb7eab3a6a99de8abbcb507be5704ae6a8994008b8a8e6b63fbd97fa8619c66b
d8665c22079939f3f63f978c5806802b22ba5bb396da9cf252ee67068bf57461bf
pkEm: 0401e9b3a83397ce01151df7c6def62d04561d5876ccc57437ca01af81a8f7a1a0
77b66d054bab46b830d7cb335db6acd7c7863a8dc2ec1840e8ac2e4e74f99fea26340040
f749f3b37512472b1da3df31854dc97a21fabad42be41ee0243613230ad69ba267669354
7ddb4d3454ac9a61d6f4ae756739a0ef226809bde93bd8b19d14cb06
skEm: 01eff8f7d9947cd83b8bcdac34496ee25dce30995df80ce64458acadfc9bacf709
8a4db0a1132524708b76c46041684ce62ce0adae54ce4d54446583357badbed08e
ikmR: 2e99ac709379c7eb15ca068253bbae4dd6297c2397f47a89b8cb3ef4e83f235f83
cb1ce3d2f754c47431ff0d0d8d2c429a7b6768d9524c3be60b9fb7749c49cb816b
pkRm: 04017b4d008b6602cf87554f1ae3f97c647da3ad5f347d73124495c6817d14f75c
181c07519bf2988a37e14967ca10254364678268c6558714d8ff6d4d821bb4f523d101c5
5f6d4f9ab0d4bce925444e2219a2b0f96920051294ef36b03dd4c69bd332df0d884794d4
4f0eb2d5ad7af9396dc946d8e4a5325724a2f8f9d6b52cba7524b644
skRm: 0015a422d63f675c687ccf900778c6da65b8941f939e1a2ec04e94d03668eddb6e
26f0ace5945388a0af1788afabe4d774160a5cc77dfc4abf6e4294125f0cf6ca8c
enc: 0401e9b3a83397ce01151df7c6def62d04561d5876ccc57437ca01af81a8f7a1a07
7b66d054bab46b830d7cb335db6acd7c7863a8dc2ec1840e8ac2e4e74f99fea26340040f
749f3b37512472b1da3df31854dc97a21fabad42be41ee0243613230ad69ba2676693547
ddb4d3454ac9a61d6f4ae756739a0ef226809bde93bd8b19d14cb06
shared_secret: bfd5bd75901d8767cd5561ac0e3b75873338517015fbd4f6b3559e8c9
f940e97ac5d4971e68c94f99934927180e01738c4f284f21109a7f4e7af9b1126589208
key_schedule_context: 007037eb32f87d04083a2f21fbda9aa88523d237843169bc66
43fe41b40f434ab776efe42da9db94c9b0b07bbab6536526de944469c381fc4f9d728b99
33adbb1015143a0ef0c7be1dca97f49c6338ddf0ad6d2d8014dcdd624e461c938d103f6c
55a6f539ca17eecf653cff7e419697dbe0e24e2697e22e738bf2c8486127f358
secret: 702aa90f69fa92790c845d3121cc2620fb96b2aba3433e95491f1620dc054287
0017388be341e19cda86a0d25e2bbfead1beda9f3d16cf0abd689944b64ee352
key: 57aeffb38c9b286367fde962c7d32bbab27075fa4d03d9a7465358d9e6fc6342
base_nonce: 61b22ddd85ce1a02ca3a89e1
exporter_secret: effa5f770620d75f76deec0f400dd42009c8088d296e58484e2a8d6
1e475d5a53639b7a909ca0651ab7787912962d2ea1e9133ed96db68fbc6cc4b9d9ab8ab2
a
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 61b22ddd85ce1a02ca3a89e1
ciphertext: 00f4bff0895c34013c8c0e153a647e8c7aaf494a61da3f88e127cadbd628
e46351f59574834a7081ebbf98536e

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 61b22ddd85ce1a02ca3a89e0
ciphertext: de0ddf5e9e229008da337d718b48096ef8f74d2332806c3cc0a9e32858ad
aad88193ee26867bd63947c19149a8

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 61b22ddd85ce1a02ca3a89e3
ciphertext: 384ae15d9a021d1b77d43657b176ea635807f29ff8bd79fd4dd05003f64c
6d8f48d281d4b1e7dea1f6e5434547

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 61b22ddd85ce1a02ca3a89e5
ciphertext: 505456abc31145bb5301d3e572465f7e8f6f20864dac6f1dd27962848c4e
eea9d553ad3dabbae88d687cfcd40b

~~~

### PSK Setup Information
~~~
mode: 1
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: ae300665d34d5ab7c0508a94a741ba2cb285966106ba9cefbe1f9c24c3eb626108
d0c9ccc8291d90c50c6d04ac181ccd8efc2cc52383eb205637a84d2be5362bf247
pkEm: 0401d8e07d90353867160b4e991c5365817bcbe07fe611b9e2d51b2be2913c47a0
8352e71d8b7da2e1726a4c9acef0b2dbf7beae263f0477e5829bd1a11b674553548f01ea
bac3a36e6830582423f095c055f109f88d4df217566f4c42c6c3696b7f8236563d868115
1566473ac4a9ebb3ce92d91a31b4c20129318df6cc9c641d86ca9c90
skEm: 01ffc6d8afae89c110b7f709d7b7a42f1f14f0d25ab0e72bc6ac74b4d71414d5a3
726d45d1550d8240807683fae156ca6ff3f2f40a0f11e0e793722f52303428a452
ikmR: dbbda5e5a54ee85cfe076e4746ceb971bed338a7fe0b625d6c7c28b3c82c812825
8906a52543655ecb62889e9dbe8feec747d06e4216f88ca4adba200179e0e75276
pkRm: 040186c1b7bf3e57c5eb7443be70506d9f70a4915e63b25b9a9859953ab30d3dc7
c97792f93cc7c1371421b1473ae13482a1c57c36b79d2f29c862f307dc8d19c8d30a01cb
116e09d7222fde60863619246eebd883bec14fb4b12ef01d232b2450d654ea304f236749
3b981bbe235128b3e176b9fecd0c3e3b7736f0fe5a999abaa0dc65e5
skRm: 0129cc1a3ddf1fb2482672893bed0f2a4e496a300bf277bdc865df261ce35bb92a
c647d035ac895dc3f0644951b21034507c12fea6c1e5c232bf89517915be461432
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 0401d8e07d90353867160b4e991c5365817bcbe07fe611b9e2d51b2be2913c47a08
352e71d8b7da2e1726a4c9acef0b2dbf7beae263f0477e5829bd1a11b674553548f01eab
ac3a36e6830582423f095c055f109f88d4df217566f4c42c6c3696b7f8236563d8681151
566473ac4a9ebb3ce92d91a31b4c20129318df6cc9c641d86ca9c90
shared_secret: 120dea3ab9b56455b80374486ae081ca65074ba5fc0e052d64eb26961
4e7f5641a2cca92f23e616a24bcb3d70fbd6092907463defa85ad19c8a5e42faca7b176
key_schedule_context: 011b6c4c7206605da6ce250983c276ee8064ddf2e60a62feb6
97a5ca87ccf078a197c945aebad60fe7ea5a7f7ff722f3f6611f6eb1d95a8696ef33ddc6
970e224d15143a0ef0c7be1dca97f49c6338ddf0ad6d2d8014dcdd624e461c938d103f6c
55a6f539ca17eecf653cff7e419697dbe0e24e2697e22e738bf2c8486127f358
secret: aecbb961a62332682f170a27661f814a8bf5514eccc9967be90f157158f6341a
368fc9feb8c3e158ad127de57f093c5a58aa44138ef8fcbca5b6faeacb4cb374
key: 420619b93c512bd517df22fc43ea0047607c74b355b17cd69aef81edc6a607f7
base_nonce: 62e63c29f06399a0c81e907e
exporter_secret: 527430fac6f9ff3839fa2e3af11b9fa74857261288d01a702d753eb
acd5b2bee52359df82dcdf637182d4d12a3c4efd3c513dac6f9fea685d10fcb5e5f87d1e
2
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 62e63c29f06399a0c81e907e
ciphertext: 17228870d1a4a692249cdadc1807fa64b8f3397e9102d56b213c2cccaae0
11b84326cebd8a948eff2027d15219

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 62e63c29f06399a0c81e907f
ciphertext: c2043ce47420e6c40bd86aa434ea65e783aab6d28164d460946bca2bda75
649b6ceb28cb407ad1a056ef4222d9

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 62e63c29f06399a0c81e907c
ciphertext: b699b9a7eb0ef210e3fc13fa91f229de31e7daec521e4ceea13534dbf7d5
cfecff5ab8ee20a87172d0000b897c

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 62e63c29f06399a0c81e907a
ciphertext: b01d1cca369f3d8fc294297c87ec2574cb646983a805e286eb7ad3496217
5e97a0a97903392b2a5c07b12184da

~~~

### Auth Setup Information
~~~
mode: 2
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 11c0c7337b294452826e14a7f6c9e7981a03c467a08f47a8b478b37f3e9c902668
98e3c3f8e84235a6a2837269c84b355d7f5ca133085172a08f00c3857da8a1410b
pkEm: 0400a424aad6b5ec7820349705e14b82e81df8a7204c71278367ae02365789f797
e00799f3f992e976c57b639451881ce5f1617f481e933d269f98cd482777cfc1f0bf018b
76cff256c43f6c84c59de83a549f25562de0b9514b206f7c3121a87da07296e13fed69f2
9be40f8e42a02c5f2e040a2594be42d9fc9498da036e510095702710
skEm: 0171b89c464a24cd554dd256038a40afee2b84fab35be25de7379281e8d9d94f30
58eefaaf30de7677c72137a4fc7fb663c7792fa10051811d58f38fc6038b9fd322
ikmR: bb56b3452a80ad82b2d48c19ce76194a198eefdb67040959bc9e479db0682a4b5b
46d7d020df66864d374b25deb5927144e3f08f2f9eacdd5f54b8b5c65d91ee211f
pkRm: 04014e2183dd2d23116fc3b6af53d7bc384337c6c78d897a2dc2e86997dcaf6bc8
68edc3ffc369922a6579f16bc3ef22eb331f72af62ac22435a8c3be602754d4ebcab01bb
42d322ab634f723bf99f6a25fbbdbd655813a95b1833a64f831f7a20dc9fe14f31ba4769
0d57d6ea52ae9182d4af7012d568773187a52e9976268c6320940312
skRm: 01c7c4a357c1d76f44fcb9e59585251cddabbb46605f0149bcf49969982f233b82
4988647e7d1e745c588f04294f042f375f9a39bde25a62e52417b471913e8c823e
ikmS: bab663b9c05f680f401a494ae8c8714fd95cbcd56a01e9e8194b4b3da863a5e831
3d4916dc58f6d3aaa2dafe420ae81b2a6c0075223afc6b13f3734a26ca30da5e38
pkSm: 0400b9defb2405e3c15772778f9dd6db4361486d803c841c82bcdba53c38dd4876
23cf293068dfd6e6ee65ab4af2a3d57b43c9c0449592daeddd39e64af5a55e65afc0010a
27fd34ea16887043092803e0c4fd179c9ca7401da4d96ff8d5f8346960623c6c542697c9
5d1108ad6df225391510b2b105f7864e4627f81b452188961a9459b4
skSm: 01f38e7318eebab0631f6d6dd58196ad7692da9b103e93d401321fb82934c0a538
d034393bac0204bd9846f86a54cbcee50bfad34835cde2f4f559a65b380d8cec9c
enc: 0400a424aad6b5ec7820349705e14b82e81df8a7204c71278367ae02365789f797e
00799f3f992e976c57b639451881ce5f1617f481e933d269f98cd482777cfc1f0bf018b7
6cff256c43f6c84c59de83a549f25562de0b9514b206f7c3121a87da07296e13fed69f29
be40f8e42a02c5f2e040a2594be42d9fc9498da036e510095702710
shared_secret: 5a294001a51d42d798d42c0a45b94a35a83d8feeadbc3199669749d93
0416c22207c1a351cdf72588fe4cc2e1d0ec8c74bee5ab542aa03671de78e92725d967e
key_schedule_context: 027037eb32f87d04083a2f21fbda9aa88523d237843169bc66
43fe41b40f434ab776efe42da9db94c9b0b07bbab6536526de944469c381fc4f9d728b99
33adbb1015143a0ef0c7be1dca97f49c6338ddf0ad6d2d8014dcdd624e461c938d103f6c
55a6f539ca17eecf653cff7e419697dbe0e24e2697e22e738bf2c8486127f358
secret: 7c6a231447448169c1d5a63fc7b27393739904ba31236022eb681ff603e007d8
a23f479f66f04a2562ebb6ebe1ed50dfeba47f9de1c19f415712de8ab08efd3a
key: e24bb29b558daeec9941ac6af01d73ec337e0bf0d5aa6140e25b4f4f1354503d
base_nonce: b692bdbed49ebb84ad17d679
exporter_secret: 40365288e3146348d6c1da7d4fb57b1fbdae5536ac8c025dc7d9d33
89d41a97f28526cc2955db087a1b9d94e609395f81c0206f360a507a32ad52f3b6b0ebd6
7
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: b692bdbed49ebb84ad17d679
ciphertext: 1ba35f7298c1fa121faa3b8e25ce0c631f59b8c73992c4dbbfcbd4b3b427
55549aa245c37329d76501d117c32d

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: b692bdbed49ebb84ad17d678
ciphertext: 4185b352ac1f15a6e84a16eda3edb48631f74aacfa8011ec9e0e0320a0f7
99a4a21a2d2c350f44b0c3fcf02ac2

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: b692bdbed49ebb84ad17d67b
ciphertext: 075144aa6db54217789f4a274b8d5e333906f83c4b2461c872c7973b05b4
9c0ec3cb185ebb1b664bebc7959ad7

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: b692bdbed49ebb84ad17d67d
ciphertext: 9908d016ca2652ed0afa4ef8ee4ee5733d20f9be933dc69ea1161825a8a9
0523ddb51ea4840e253fbdfe4df9e8

~~~

### AuthPSK Setup Information
~~~
mode: 3
kem_id: 18
kdf_id: 3
aead_id: 2
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 4ebb461a5c46330d6de3a40d19ac499cc206733cf1a4fb3ba922d976aa1c458486
68f04a3b5a4845a0d1c83755967d8914a9824fbb8823d161c16c93c51636e1ad89
pkEm: 04005ecbb8a44f65b079fb6a025d0ed2a7c675113836b5143f7886bcf89cfb2cf0
d26672874fb03124e0e6303cdecb139f964e78169aff79d7f57feebc66cf58747a3f010b
14f67c282b091a5aefc87672951e5ddcb9f04897320a43c5aab8b9d03f1fc00a0c2f8b5a
f41abece59b17ca0f8427df7cb1cf79d01ac4013179a8cc66e94cee7
skEm: 012850e41e3f14578099a650b470eb6226b1f757145e4ed98326888f87e5d1fef0
9a57a6596fe141bcc5fe4fff32620ba6b10ffae1c476985ed0ff1d96116207bf85
ikmR: 1ae2f1008c46c7a6e9275b1e29c906475c6bc019b1dfc38cbce68c5233de9d33ba
93fe9d7b9ea5beb04f4adc5a3b72238f6e3d904d29eb0680ea240103d3335a3c47
pkRm: 040161142294012f7f1e7af7ba86611de6d4cf7a7eb40498b7b40aee7ae2e9d8ac
41b6a1615e076e0ffd0239e1e465b0b791601cfb62212732820223a2ef5f0e0ab3d7002c
283a89ac436fd2967c5975b9db046c50fab2dbcc9b17de528f2d3d6ef4e520d111f433fd
d8ee7885c89215668775bce903d73f4a0253407eeec920817fa04ae8
skRm: 0038ac202327bcb0ee9e3db84302930f2963a8a5440a172600d855c07864018ff5
1a5725c8b1d9037cebf84cb53755a5f35296b603afcfbea95530361ca40076b75c
ikmS: e0f2ada4f2a900fded767dc9868119ee3e4767afac667a780b68e5e2b4d7d363db
f02717ab314369c45f34dcec3de384a65e8453a971ad0353a507f34dc1d5d9b8f5
pkSm: 0401e965e58f927c571f468a1cfeb8eaf2c906cfa9f43f3c427dc8e5b4379c70e4
20f90f86c517ff17d1eb35aa7f071e89c07523099e14f7e033087a089984deaa73a90100
bc0ee78fa5bf8d3956c1ca9d07ccc3ad6dca951108bbf0835fa2375dd3d45760b7999444
e670b73cac2622d3fd75152217b17b88dac4935820c8c5a97550b509
skSm: 0130f8092f0b7ac4571e9425c561a7f1d610d13fa6ea2ef43ca1d5451cf9c0e799
d7c95648aa3a7714c04868e7fa9dff65afcc225f94d1fefee875b5c55dc70da587
psk: 0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82
psk_id: 456e6e796e20447572696e206172616e204d6f726961
enc: 04005ecbb8a44f65b079fb6a025d0ed2a7c675113836b5143f7886bcf89cfb2cf0d
26672874fb03124e0e6303cdecb139f964e78169aff79d7f57feebc66cf58747a3f010b1
4f67c282b091a5aefc87672951e5ddcb9f04897320a43c5aab8b9d03f1fc00a0c2f8b5af
41abece59b17ca0f8427df7cb1cf79d01ac4013179a8cc66e94cee7
shared_secret: 0f5896c3a2d7323f0608291362befd1b584dae187b064a57d3fcf22a0
254c1a7c7c4baba883dca3c250747b756f8f8f051434d4d7f4b193a66f4f7b3118d39ac
key_schedule_context: 031b6c4c7206605da6ce250983c276ee8064ddf2e60a62feb6
97a5ca87ccf078a197c945aebad60fe7ea5a7f7ff722f3f6611f6eb1d95a8696ef33ddc6
970e224d15143a0ef0c7be1dca97f49c6338ddf0ad6d2d8014dcdd624e461c938d103f6c
55a6f539ca17eecf653cff7e419697dbe0e24e2697e22e738bf2c8486127f358
secret: a315a07a5a694445530ad322df119718053d7dfbaad443777bd0d30f8f62af4a
93293c9297473d1654bba218a48f476a00d3fd142ae1634d84296071e51829a9
key: ca510f3500c9050ca1b21b958464296bb16baceb4dee8fa6a3076a2430423d0a
base_nonce: 37abf56907992ad40e27ed50
exporter_secret: f83d533341fb594fa6e2c4004fd10d73c9e939c7305a7ced4b92a64
904ed0602994fd00cff4e4e06ba6e45d5d685650b24162ed4a6c31d944598649fe71cd44
e
~~~

#### Encryptions
~~~
sequence number: 0
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: 37abf56907992ad40e27ed50
ciphertext: 08b11bb7c02b39a5d15fbd94e5f2f2441a0728a5a7ed91b13a97bd19d813
693ddfe97138b5412fff9ddc522801

sequence number: 1
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d31
nonce: 37abf56907992ad40e27ed51
ciphertext: 32436c4a18f3d2cce9d20a38f9dc0ec2865785475b83a40a75836663303a
70fcdecfd963258e00d6fccd9663e6

sequence number: 2
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d32
nonce: 37abf56907992ad40e27ed52
ciphertext: 6994cd7137222f9433bac62ad841833e7ecd0aa948db67177ed21ad5a1c5
105a38f15a883a3412c13da16aef1a

sequence number: 4
plaintext: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d34
nonce: 37abf56907992ad40e27ed54
ciphertext: cf5d16f80af79584cb3333c2bc86fe2e5ef33d4abc3292c45f6481c85af8
6ddeb62ca7cb5a2dd32c59e9a6ecfa

~~~
