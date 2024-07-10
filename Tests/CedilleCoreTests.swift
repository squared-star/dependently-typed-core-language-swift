import XCTest
@testable import CedilleCore

final class CedilleCoreTests: XCTestCase {
    func testParseIdentityFunction() throws {
        let term = try Term.parse(code: "Λ A : Type. λ x : A. x")

        XCTAssertEqual(
            term,
            .λ(
                parameter: Parameter(
                    name: "A",
                    type: .type,
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
            )
        )
        XCTAssertEqual(
            term.infer(
                in: Context.empty
            ),
            .success(
                Term.function(
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
    }

    func testParseNamedIdentityFunction() throws {
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
    }

    func testSemigroupLambdaEncoded() throws {
        let semigroup = try Term.parse(code:
            """
            𝐥𝐞𝐭 Associative = Λ G : Type. λ combine : G → G → G.
                x:G → y:G → z:G → |combine x (combine y z) = combine (combine x y) z| 𝐢𝐧
            𝐥𝐞𝐭 Semigroup = ⋂ R : Type. (⋂ G : Type. combine:(G → G → G) → associativity:Associative {G} combine → R) → R 𝐢𝐧
            Semigroup
            """)
        XCTAssertEqual(
            semigroup,
            Term.reference(
                Reference(
                    name: "Semigroup",
                    term: .function(
                        parameter: Parameter(
                            name: "R",
                            type: .type,
                            representation: .erased
                        ),
                        returnType: .function(
                            parameter: Parameter(
                                name: "",
                                type: .function(
                                    parameter: Parameter(
                                        name: "G",
                                        type: .type,
                                        representation: .erased
                                    ),
                                    returnType: .function(
                                        parameter: Parameter(
                                            name: "combine",
                                            type: .function(
                                                parameter: Parameter(
                                                    name: "",
                                                    type: .variable(
                                                        index: 0
                                                    ),
                                                    representation: .normal
                                                ),
                                                returnType: .function(
                                                    parameter: Parameter(
                                                        name: "",
                                                        type: .variable(
                                                            index: 1
                                                        ),
                                                        representation: .normal
                                                    ),
                                                    returnType: .variable(
                                                        index: 2
                                                    )
                                                )
                                            ),
                                            representation: .normal
                                        ),
                                        returnType: .function(
                                            parameter: Parameter(
                                                name: "associativity",
                                                type: .application(
                                                    function: .application(
                                                        function: .reference(
                                                            Reference(
                                                                name: "Associative",
                                                                term: .λ(
                                                                    parameter: Parameter(
                                                                        name: "G",
                                                                        type: .type,
                                                                        representation: .erased
                                                                    ),
                                                                    body: .λ(
                                                                        parameter: Parameter(
                                                                            name: "combine",
                                                                            type: .function(
                                                                                parameter: Parameter(
                                                                                    name: "",
                                                                                    type: .variable(
                                                                                        index: 0
                                                                                    ),
                                                                                    representation: .normal
                                                                                ),
                                                                                returnType: .function(
                                                                                    parameter: Parameter(
                                                                                        name: "",
                                                                                        type: .variable(
                                                                                            index: 1
                                                                                        ),
                                                                                        representation: .normal
                                                                                    ),
                                                                                    returnType: .variable(
                                                                                        index: 2
                                                                                    )
                                                                                )
                                                                            ),
                                                                            representation: .normal
                                                                        ),
                                                                        body: .function(
                                                                            parameter: Parameter(
                                                                                name: "x",
                                                                                type: .variable(
                                                                                    index: 1
                                                                                ),
                                                                                representation: .normal
                                                                            ),
                                                                            returnType: .function(
                                                                                parameter: Parameter(
                                                                                    name: "y",
                                                                                    type: .variable(
                                                                                        index: 2
                                                                                    ),
                                                                                    representation: .normal
                                                                                ),
                                                                                returnType: .function(
                                                                                    parameter: Parameter(
                                                                                        name: "z",
                                                                                        type: .variable(
                                                                                            index: 3
                                                                                        ),
                                                                                        representation: .normal
                                                                                    ),
                                                                                    returnType: .equal(
                                                                                        .application(
                                                                                            function: .application(
                                                                                                function: .variable(
                                                                                                    index: 3
                                                                                                ),
                                                                                                argument: .variable(
                                                                                                    index: 2
                                                                                                ),
                                                                                                representation: .normal
                                                                                            ),
                                                                                            argument: .application(
                                                                                                function: .application(
                                                                                                    function: .variable(
                                                                                                        index: 3
                                                                                                    ),
                                                                                                    argument: .variable(
                                                                                                        index: 1
                                                                                                    ),
                                                                                                    representation: .normal
                                                                                                ),
                                                                                                argument: .variable(
                                                                                                    index: 0
                                                                                                ),
                                                                                                representation: .normal
                                                                                            ),
                                                                                            representation: .normal
                                                                                        ),
                                                                                        .application(
                                                                                            function: .application(
                                                                                                function: .variable(
                                                                                                    index: 3
                                                                                                ),
                                                                                                argument: .application(
                                                                                                    function: .application(
                                                                                                        function: .variable(
                                                                                                            index: 3
                                                                                                        ),
                                                                                                        argument: .variable(
                                                                                                            index: 2
                                                                                                        ),
                                                                                                        representation: .normal
                                                                                                    ),
                                                                                                    argument: .variable(
                                                                                                        index: 1
                                                                                                    ),
                                                                                                    representation: .normal
                                                                                                ),
                                                                                                representation: .normal
                                                                                            ),
                                                                                            argument: .variable(
                                                                                                index: 0
                                                                                            ),
                                                                                            representation: .normal
                                                                                        )
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                ),
                                                                clos: false
                                                            )
                                                        ),
                                                        argument: .variable(
                                                            index: 1
                                                        ),
                                                        representation: .erased
                                                    ),
                                                    argument: .variable(
                                                        index: 0
                                                    ),
                                                    representation: .normal
                                                ),
                                                representation: .normal
                                            ),
                                            returnType: .variable(
                                                index: 3
                                            )
                                        )
                                    )
                                ),
                                representation: .normal
                            ),
                            returnType: .variable(
                                index: 1
                            )
                        )
                    ),
                    clos: false
                )
            )
        )
        

      
        XCTAssertEqual(semigroup.infer(in: .empty), .success(.type))
    }

}
