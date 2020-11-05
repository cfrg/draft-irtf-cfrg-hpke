# Hybrid Public Key Encryption

This is the working area for the individual Internet-Draft, "Hybrid Public Key Encryption".

* [Editor's Copy](https://cfrg.github.io/draft-irtf-cfrg-hpke/#go.draft-irtf-cfrg-hpke.html)
* [Individual Draft](https://tools.ietf.org/html/draft-irtf-cfrg-hpke)
* [Compare Editor's Copy to Individual Draft](https://cfrg.github.io/draft-irtf-cfrg-hpke/#go.draft-irtf-cfrg-hpke.diff)

## Building the Draft

Formatted text and HTML versions of the draft can be built using `make`.

```sh
$ make
```

This requires that you have the necessary software installed.  See
[the instructions](https://github.com/martinthomson/i-d-template/blob/master/doc/SETUP.md).

# Existing HPKE implementations

| Implementation                                     | Language | Version  | Modes  |
| -------------------------------------------------- |:---------|:---------|:-------|
| [go-hpke](https://github.com/cisco/go-hpke)        | Go       | draft-06 | All    |
| [rust-hpke](https://github.com/rozbb/rust-hpke)    | Rust     | draft-06 | All    |
| [BoringSSL](https://boringssl.googlesource.com/boringssl/+/HEAD/crypto/hpke/) | C | draft-05 | Base, PSK |
| [NSS](https://hg.mozilla.org/projects/nss/file/tip/lib/pk11wrap) | C | draft-05 | Base, PSK |

Submit a PR if you would like your implementation to be added!

## Contributing

See the
[guidelines for contributions](https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/master/CONTRIBUTING.md).
