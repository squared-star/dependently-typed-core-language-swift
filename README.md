# A dependently-typed core language in Swift

## Overview

CedilleCore is a Swift implementation of Cedille Core dependent type theory. This project provides foundational components to work with dependent types, intersection types, and type checking.

## Features

- **Term Representation**: Define and manipulate various terms such as types, functions, applications, and more.
- **Support for both erased and normal parameter passing**: Manage function parameters with different representations.
- **Bidirectional Type Checking**: Perform type checking with detailed error handling. The API supports check as well as infer modes; however, the parser does not support type annotations in arbitrary places to truly give the user flexibility on where the place type annotations and where they omit them.
- **Context Management**: Maintain a context of variables for accurate type inference and checking.

## Usage

### Example

Here is an example of what implementing a Semigroup from abstract algebra looks like in this implementation of `CedilleCore`:

```text
𝐥𝐞𝐭 Associative = Λ G : Type. λ combine : G → G → G.
    x:G → y:G → z:G → |combine x (combine y z) = combine (combine x y) z| 𝐢𝐧
𝐥𝐞𝐭 Semigroup = ⋂ R : Type. (⋂ G : Type. combine:(G → G → G) → associativity:Associative {G} combine → R) → R 𝐢𝐧
Semigroup
```

### Advanced Example

Here is a snippet from a test case that demonstrates how to use the API:

```swift
let term = try Term.parse(
    code: "𝐥𝐞𝐭 id = Λ A : Type. λ x : A. x 𝐢𝐧 id"
)
XCTAssertEqual(
    term,
    .reference(
        Reference(
            name: "id",
            term: Term.λ(
                parameter: Parameter(
                    name: "A",
                    type: Term.type,
                    representation: .erased
                ),
                body: .λ(
                    parameter: Parameter(
                        name: "x",
                        type: .variable(
                            index: 0
                        ),
                        representation: .normal
                    ),
                    body: .variable(
                        index: 0
                    )
                )
            ),
            clos: false
        )
    )
)
XCTAssertEqual(
    term.infer(
        in: .empty
    ),
    .success(
        .function(
            parameter: Parameter(
                name: "A",
                type: .type,
                representation: .erased
            ),
            returnType: .function(
                parameter: Parameter(
                    name: "x",
                    type: .variable(
                        index: 0
                    ),
                    representation: .normal
                ),
                returnType: .variable(
                    index: 1
                )
            )
        )
    )
)
```

## License

This project is licensed under the AGPLv3 License. See the [LICENSE](LICENSE) file for details.

## Acknowledgements

This project draws major inspiration from the following sources:

- [Implementing a Type Checker in Haskell](https://davidchristiansen.dk/tutorials/implementing-types-hs.pdf) by David Christiansen - For helping understand and develop the first bidirectional type checker.
- [Cedille Core](https://github.com/VictorTaelin/Cedille-Core) - For providing foundational ideas and approaches in implementing a dependent type checker.
- [Cedille](https://github.com/cedille/cedille) - For inspiring the dependent type theory implemented in this project, which is a variation of Cedille Core.
