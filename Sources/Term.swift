import Foundation
import Strix

/*
Example:
-- Rust-style notation: type ChurchNatural = fn<a> (a, a → a) → a;
𝐥𝐞𝐭 ChurchNatural : Type = ⋂ a : Type. a → (a → a) → a 𝐢𝐧
𝐥𝐞𝐭 churchSuccessor :  ChurchNatural → ChurchNatural =
    λ n : ChurchNatural. Λ a : Type. λ z : a. λ s : a → a. s (n a z s) 𝐢𝐧
𝐥𝐞𝐭 churchZero : ChurchNatural = Λ a : Type. λ z : a. λ s : a → a. z 𝐢𝐧
𝐥𝐞𝐭 Inductive : ChurchNatural → Type = λ n : ChurchNatural.
    ⋂ p : ChurchNatural → Type. p churchZero → (⋂ n : ChurchNatural. p n → p (churchSuccessor n)) → p n 𝐢𝐧
𝐥𝐞𝐭 Natural : Type = ⟨n : ChurchNatural⟩ Inductive n 𝐢𝐧
𝐥𝐞𝐭 inductiveZero : Inductive churchZero = Λ p : ChurchNatural → Type. λ z : p churchZero.
    λ s : ⋂ n : ChurchNatural. p n → p (churchSuccessor n). z 𝐢𝐧
𝐥𝐞𝐭 inductiveSuccessor : ⋂ cn : ChurchNatural. Inductive cn → Inductive (churchSuccessor cn) =
    Λ m : ChurchNatural. λ im : Inductive m. Λ P : ChurchNatural → Type. λ base : P churchZero. λ step : ⋂ n : ChurchNatural. P n → P (churchSuccessor n). step m (im base step) 𝐢𝐧
𝐥𝐞𝐭 zero : Natural = {churchZero, inductiveZero} ∈ Natural 𝐢𝐧
𝐥𝐞𝐭 successor : Natural → Natural = λ n : Natural.
    𝐥𝐞𝐭 {church : ChurchNatural, inductive : Inductive church} = n 𝐢𝐧
    {churchSuccessor church, inductiveSuccessor church inductive} ∈ Natural 𝐢𝐧

successor (successor zero)
*/
/// A Representation specifies if a term is erased or not.
public enum Representation: Equatable, Hashable {
    /// Syntax: `⋂ x : A. B(x)`
    case erased

    /// Syntax: `x:A → B(x)`
    case normal
}

/// Defines a parameter in a function type or lambda abstraction.
public struct Parameter {
    let name: String
    var type: Term
    let representation: Representation
}

extension Parameter {

    /// Substitutes a term in the parameters type.
    /// - Parameters:
    ///   - term: The term to substitute.
    ///   - depth: The depth of the substitution.
    /// - Returns: The parameter with the substituted type.
    func substitute(_ term: Term, at depth: Int) -> Parameter {
        var parameter = self
        parameter.type = type.substitute(term, at: depth)
        return parameter
    }
    // TODO: improve explanation of exceptBind
    /// Evaluates the parameter.
    /// - Parameter exceptBind: If true, the parameter is not evaluated if it is a bind.
    /// - Returns: The evaluated parameter.
    func evaluate(exceptBind: Bool) -> Parameter {
        var result = self
        result.type = self.type.evaluate(exceptBind: exceptBind)
        return result
    }
}

/// Heap allocated type information for a reference.
/// - Note: This is used to cache type information for references.
public class CachedTypeInfo {
    var type: Attempt<Term, TypeErrors>?
    init(typeInfo: Attempt<Term, TypeErrors>?) {
        type = typeInfo
    }
}

/// Named reference to a term.
public struct Reference {
    let name: String
    var term: Term
    let clos: Bool
    let typeInfo: CachedTypeInfo

    /// Initializes a reference.
    /// - Parameters:
    ///   - name: The name of the reference.
    ///   - term: The term the reference refers to.
    ///   - clos: if the term is closed i.e. has no variables bound outside of it used.
    public init(name: String, term: Term, clos: Bool) {
        self.name = name
        self.term = term
        self.clos = clos
        self.typeInfo = CachedTypeInfo(typeInfo: nil)
    }

}

extension Reference {
    /// Type checks the reference and caches the type information.
    /// - Parameter context: The context to type check the reference in.
    /// - Returns: The type of the reference.
    /// - Note: If the type information is already cached, it is returned.
    func check(in context: Context) -> Attempt<Term, TypeErrors> {

        guard let type = typeInfo.type else {
            let checkAttempt = term.check(in: context)
            self.typeInfo.type = checkAttempt
            return checkAttempt
        }
        return type
    }

    func check(is type: Term, in context: Context) -> Attempt<Void, TypeErrors> {
        guard let knownType = self.typeInfo.type else {
            return self.term.check(is: type, in: context)
        }
        return knownType.flatMap { knownType in

            guard knownType ⊆ type else {
                return .failure(TypeErrors(error: .typeMismatch(expected: type, actual: knownType, for: self.term, in: self.term)))
            }

            return .success(())
        }
    }

    /// Infers the type of the reference and caches the type information.
    /// - Parameter context: The context to infer the reference in.
    /// - Returns: The inferred type of the reference.
    func infer(in context: Context) -> Attempt<Term, TypeErrors> {
        guard let type = typeInfo.type else {
            let checkAttempt = term.infer(in: context)
            self.typeInfo.type = checkAttempt
            return checkAttempt
        }
        return type
    }
}

extension Reference: Equatable {
    /// Compares two references.
    /// - Parameters:
    ///   - lhs: The left hand side reference.
    ///   - rhs: The right hand side reference.
    /// - Returns: True if the references are equal, false otherwise.
    public static func ==(lhs: Reference, rhs: Reference) -> Bool {
        lhs.term == rhs.term
    }
}

/// A variable in a context.
struct Variable {
    let name: String
    var term: Term
}

extension Variable: Equatable {

    /// Compares two variables.
    /// - Parameters:
    ///   - lhs: The left hand side variable.
    ///   - rhs: The right hand side variable.
    /// - Returns: True if the variables are equal, false otherwise.
    static func ==(lhs: Variable, rhs: Variable) -> Bool {
        lhs.name == rhs.name && lhs.term == rhs.term
    }
}

extension Variable: Hashable {

    /// Hashes the variable.
    /// - Parameter hasher: The hasher to use.
    func hash(into hasher: inout Hasher) {
        hasher.combine(name)
        hasher.combine(term)
    }
}

/// A Cedille Core term.
public enum Term {
    /// Syntax: `Type`
    case type
    case variable(index: Int)

    /// Syntax: `f x y
    indirect case application(function: Term, argument: Term, representation: Representation)

    /// Syntax: `x:A -> B x`
    /// Syntax: `⋂ x : A. B x`
    indirect case function(parameter: Parameter, returnType: Term)

    /// Syntax: `λ x : A. g x y`
    /// Syntax: `Λ x : A. B x`
    indirect case λ(parameter: Parameter, body: Term)

    /// Syntax: `⟨x : A⟩ B x`
    indirect case intersection(name: String, type0: Term, type1: Term)

    /// Syntax: `{x, y} ∈ t`
    indirect case both(type: Term, value0: Term,  value1: Term)

    /// Syntax for now: `⓿ x`
    /// In the surface language, there will be a pattern matching syntax for this.
    indirect case first(Term)

    /// Syntax for now: `❶ x`
    /// In the surface language, there will be a pattern matching syntax for this.
    indirect case second(Term)

    /// Syntax: `|a = b|`
    indirect case equal(Term, Term)

    /// Syntax:
    /// `𝐫𝐞𝐟𝐥 t 𝐚𝐬 k`
    indirect case reflexive(of: Term, as: Term)

    /// Syntax: `𝐬𝐲𝐦 e`
    indirect case symmetry(Term)


    /// Syntax `𝐮𝐬𝐢𝐧𝐠 e 𝐫𝐞𝐰𝐫𝐢𝐭𝐞 x 𝐢𝐧 P x ∋ t`
    indirect case rewrite(name: String, type: Term, proof: Term, term: Term)

    /// syntax: `𝐜𝐚𝐬𝐭 b 𝐭𝐨 𝐭𝐲𝐩𝐞 𝐨𝐟 a 𝐮𝐬𝐢𝐧𝐠 e`
    indirect case cast(proof: Term, value0: Term, value1: Term)

    /// For caching type information and preserving names.
    indirect case reference(Reference)

    static func application(function: Term, arguments: [(argument: Term, representation: Representation)]) -> Term {
        return arguments.reduce(function) { function, argument in Term.application(function: function, argument: argument.argument, representation: argument.representation)}
    }

    //static func `let`(name: String, type: Term, be value: Term, in body: Term) -> Term

}

/// Represents the TypeErrors that can occur during type checking.
public enum TypeError: Equatable {
    case typeMismatch(expected: Term, actual: Term, for: Term, in: Term) // TODO: add source location information to term
    case untypable(Term, expected: Term, in: Term)
    case nonfunctionApplication(nonfunction: Term, argument: Term, context: Context)
    case representationMismatch(expected: Representation, actual: Representation, in: Term, given: Context)
    case invalidArgument(function: Term, argument: Term, expected: Term, actual: Term, given: Context)
    case invalidBothType(in: Term, given: Context)
    case cannotDetermineType(for: Term)
    case unequalViews(of: Term, view0: Term, view1: Term, given: Context)
    case substitutionFailed(in: Term, of: Term, dueTo: TypeErrors?, given: Context)
    case nonIntersectionView(nonintersection: Term, given: Context)
    case nonequalitySymmetry(nonequality: Term)
    case nonequalityRewrite(nonequality: Term, given: Context)
    case nonequalityCast(nonequality: Term, given: Context)
    case invalidEqualityProof(proof: Term, given: Context)

    /// Compares two type errors.
    /// - Parameters:
    ///   - lhs: The left hand side type error.
    ///   - rhs: The right hand side type error.
    /// - Returns: True if the type errors are equal, false otherwise.
    public static func == (lhs: TypeError, rhs: TypeError) -> Bool {
        switch (lhs, rhs) {
        case let (.typeMismatch(expected1, actual1, for1, in1), .typeMismatch(expected2, actual2, for2, in2)):
            return expected1 == expected2 && actual1 == actual2 && for1 == for2 && in1 == in2
        case let (.untypable(term1, expected1, in1), .untypable(term2, expected2, in2)):
            return term1 == term2 && expected1 == expected2 && in1 == in2
        case let (.nonfunctionApplication(nonfunction1, argument1, context1), .nonfunctionApplication(nonfunction2, argument2, context2)):
            return nonfunction1 == nonfunction2 && argument1 == argument2 && context1 == context2
        case let (.representationMismatch(expected1, actual1, in1, given1), .representationMismatch(expected2, actual2, in2, given2)):
            return expected1 == expected2 && actual1 == actual2 && in1 == in2 && given1 == given2
        case let (.invalidArgument(function1, argument1, expected1, actual1, given1), .invalidArgument(function2, argument2, expected2, actual2, given2)):
            return function1 == function2 && argument1 == argument2 && expected1 == expected2 && actual1 == actual2 && given1 == given2
        case let (.invalidBothType(in1, given1), .invalidBothType(in2, given2)):
            return in1 == in2 && given1 == given2
        case let (.cannotDetermineType(for1), .cannotDetermineType(for2)):
            return for1 == for2
        case let (.unequalViews(of1, view01, view11, given1), .unequalViews(of2, view02, view12, given2)):
            return of1 == of2 && view01 == view02 && view11 == view12 && given1 == given2
        case let (.substitutionFailed(in1, of1, dueTo1, given1), .substitutionFailed(in2, of2, dueTo2, given2)):
            return in1 == in2 && of1 == of2 && dueTo1 == dueTo2 && given1 == given2
        case let (.nonIntersectionView(nonintersection1, given1), .nonIntersectionView(nonintersection2, given2)):
            return nonintersection1 == nonintersection2 && given1 == given2
        case let (.nonequalitySymmetry(nonequality1), .nonequalitySymmetry(nonequality2)):
            return nonequality1 == nonequality2
        case let (.nonequalityRewrite(nonequality1, given1), .nonequalityRewrite(nonequality2, given2)):
            return nonequality1 == nonequality2 && given1 == given2
        case let (.nonequalityCast(nonequality1, given1), .nonequalityCast(nonequality2, given2)):
            return nonequality1 == nonequality2 && given1 == given2
        case let (.invalidEqualityProof(proof1, given1), .invalidEqualityProof(proof2, given2)):
            return proof1 == proof2 && given1 == given2
        default:
            return false
        }
    }
}

/// A non-empty list of type errors.
public struct TypeErrors: Error, Equatable {
    var errors: [TypeError] // TODO: use better data structure

    /// Initializes a new `TypeErrors` instance with the given error.
    init(error: TypeError) {
        self.errors = [error]
    }
}


extension TypeErrors: Semigroup {

    /// Combines two `TypeErrors` instances.
    /// - Parameters:
    ///   - lhs: The left hand side `TypeErrors` instance.
    ///   - rhs: The right hand side `TypeErrors` instance.
    /// - Returns: A new `TypeErrors` instance with the combined errors.
    public static func combined(_ lhs: @autoclosure () -> Self, _ rhs: @autoclosure () -> Self) -> Self {
        var lhs = lhs()
        lhs.errors.append(contentsOf: rhs().errors)
        return lhs
    }

    /// Combines the given `TypeErrors` instance with the current instance.
    /// - Parameter additionalErrors: The `TypeErrors` instance to combine with.
    /// - Returns: A new `TypeErrors` instance with the combined errors.
    public mutating func combine(with additionalErrors: @autoclosure () -> TypeErrors) {
        errors.append(contentsOf: additionalErrors().errors)
    }
}

/// A type that can be combined with another instance of the same type while
/// obeying associativity excluding out of memory problems.
/// Law: `combined(x, combined(y, z)) == combined(combined(x, y), z)`
public protocol Semigroup /*TODO: ~Copyable */{

    /// Combines two instances of the type.
    /// - Parameters:
    ///   - lhs: The left hand side instance.
    ///   - rhs: The right hand side instance.
    /// - Returns: A new instance of the type with the combined values.
    static func combined(_ lhs: @autoclosure () -> Self, _ rhs: @autoclosure () -> Self) -> Self

    /// Combines the given instance with the current instance.
    /// - Parameter with: The instance to combine with.
    /// - Returns: A new instance of the type with the combined values.
    mutating func combine(with: @autoclosure () -> Self)
}

/// Operator for combining two instances of a `Semigroup` type.
infix operator ⋅

/// Combines two instances of a `Semigroup` type.
/// - Parameters:
///   - lhs: The left hand side instance.
///   - rhs: The right hand side instance.
/// - Returns: A new instance of the type with the combined values.
func ⋅<G: Semigroup>(lhs: @autoclosure () -> G, rhs: @autoclosure () -> G) -> G {
    return G.combined(lhs(), rhs())
}

/// A type that can be combined with another instance of the same type while
/// obeying associativity and has a neutral element.
/// Law: `combined(x, combined(y, z)) == combined(combined(x, y), z)`
protocol Monoid : Semigroup /* TODO: ~Copyable */ {

    /// The neutral element of the type.
    static var neutral: Self { get }

    /// Combines the given instance with the current instance. After the method is done, self will be
    /// equal to the combined value, and the used instance will be equal to the neutral element.
    /// - Parameter using: The instance to combine with. This is set to netural after the method is done.
    mutating func combine(using: inout Self)

    /// Combines the given instance with the current instance. After the method is done, self will be the netural
    /// element and into labelled argument will contain the combined value.
    /// - Parameter into: The instance to combine with. This is set to netural after the method is done.
    mutating func combine(into: inout Self)
}

/// A type like `Result` that can represent either a success or a failure, but also a partial success/failure where the
/// expected result is known, but there are errors.
public enum Attempt<Success, Failure> {

    /// Represents a failure.
    case failure(Failure)

    /// Represents a partial success or failure.
    case partial(expected: Success, error: Failure)

    /// Represents a success.
    case success(Success)
}
extension Attempt: Equatable
where
    Success: Equatable, Failure: Equatable
{}

extension Attempt {

    /// The error of the attempt, if any.
    var error: Failure? {
        switch self {
        case .failure(let e): return e
        case .partial(expected: _, error: let e): return e
        case .success(_): return nil
        }
    }

    /// The expected result of the attempt, if any.
    var expected : Success? {
        switch self {
        case .failure(_): return nil
        case .partial(let expected, error: _):
            return expected
        case .success(let result):
            return result
        }
    }

    /// Maps the expected value of the attempt to a new value.
    public func map<T>(_ transform: (Success) -> T) -> Attempt<T, Failure> {
        switch self {
        case .failure(let e): return .failure(e)
        case let .partial(expected, error): return .partial(expected: transform(expected), error: error)
        case .success(let ok): return .success(transform(ok))
        }
    }


    /// Enables sequencing attempts.
    /// - Parameters:
    ///   - transform: A closure that takes the expected value of the attempt and returns a new attempt.
    /// - Returns: A new attempt with the transformed expected value.
    public func flatMap<T>(_ transform: (Success) -> Attempt<T, Failure>) -> Attempt<T, Failure> where Failure: Semigroup {
        switch self {
        case .failure(let e): return .failure(e)
        case .success(let e): return transform(e)
        case let .partial(expected, e0):
            switch transform(expected) {
            case .failure(let e1): return .failure(e0 ⋅ e1)
            case let .partial(expected, e1): return .partial(expected: expected, error: e0 ⋅ e1)
            case .success(let result): return .partial(expected: result, error: e0)
            }
        }
    }

    /// Zips two attempts together.
    /// - Parameters:
    ///   - other: The other attempt to zip with.
    ///   - zipped: A closure that takes the expected values of the two attempts and returns a new value.
    /// - Returns: A new attempt with the zipped expected values.
    public func zip<T, R>(_ other: Attempt<T, Failure>, using zipped: (Success, T) -> R) -> Attempt<R, Failure>
    where
        Failure: Semigroup
    {
        switch (self, other) {
        case let (.success(x), .success(y)):
            return .success(zipped(x, y))
        case let (.partial(expected: x, error: e0), .success(y)), let (.success(x), .partial(expected: y, error: e0)):
            return .partial(expected: zipped(x, y), error: e0)
        case let (.partial(expected: x, error: e0), .partial(expected: y, error: e1)):
            return .partial(expected: zipped(x, y), error: e0 ⋅ e1)
        case let (.partial(expected: _, error: e0), .failure(e1)),
             let (.failure(e0), .partial(expected: _, error: e1)),
             let (.failure(e0), .failure(e1)):
            return .failure(e0 ⋅ e1)
        case (.failure(let e), .success(_)), (.success(_), .failure(let e)):
            return .failure(e)
        }
    }

    /// Zips two attempts together using a tuple.
    /// - Parameters:
    ///   - other: The other attempt to zip with.
    /// - Returns: A new attempt with the zipped expected values.
    public func zip<T>(_ other: Attempt<T, Failure>) -> Attempt<(Success, T), Failure>
    where
        Failure: Semigroup
    {
        return zip(other, using: {x, y  in (x, y)})
    }

    /// Zips two attempts together, returning the expected value of the other attempt.
    /// - Parameters:
    ///   - other: The other attempt to zip with.
    /// - Returns: A new attempt with the expected value of the other attempt.
    public func zip<T>(returning other: Attempt<T, Failure>) -> Attempt<T, Failure>
    where
        Failure: Semigroup
    {
        return zip(other, using: {_, y in y})
    }

    /// Attaches a value to the attempt.
    /// - Parameter expected: The value to attach.
    /// - Returns: A new attempt with the attached value.
    public func attach<T>(_ expected: T) -> Attempt<T, Failure> {
        switch self {
        case .success(_): return .success(expected)
        case .failure(let e), .partial(expected: _, error: let e):
            return .partial(expected: expected, error: e)
        }
    }

}

// TODO: improve error reporting
func expecting(_ expected: Term, from attempt: Attempt<Term, TypeErrors>, for term: Term, in largerTerm: Term) -> Attempt<Term, TypeErrors> {
    switch attempt {
    case .failure(let e0):
        return .partial(expected: expected, error: e0 ⋅ TypeErrors(error: .untypable(term, expected: expected, in: largerTerm)))
    case let .partial(expected: actual, error):
        if actual == expected {
            return .partial(expected: expected, error: error)
        } else {
            return .partial(expected: expected, error: error ⋅ TypeErrors(error: .typeMismatch(expected: expected, actual: actual, for: term, in: largerTerm)))
        }
    case let .success(result):
        if result == expected {
            return .success(term)
        } else {
            return .partial(expected: expected, error: TypeErrors(error: .typeMismatch(expected: expected, actual: result, for: term, in: largerTerm)))
        }

    }
}

infix operator ⊆: ComparisonPrecedence

extension Term {

    public func evaluate(exceptBind/* TODO: consider giving this a better name*/: Bool) -> Term {
        switch self {
        case .type: return .type
        case let .function(parameter, returnType):
            return .function(parameter: exceptBind ? parameter : parameter.evaluate(exceptBind: exceptBind), returnType: returnType.evaluate(exceptBind: exceptBind))
        case let .λ(parameter, body):
            if case .erased = parameter.representation {
                fatalError("TODO: erased parameters")
                //return body.evaluate(exceptBind: exceptBind).substitute(fatalError(), at: 0)
            } else {
                return .λ(parameter: parameter, body: body.evaluate(exceptBind: exceptBind))
            }
        case let .application(function, argument, representation: .erased):
            return function.evaluate(exceptBind: exceptBind)
        case let .application(function, argument, representation: .normal):
            let function = function.evaluate(exceptBind: exceptBind)
            switch function {
            case let .λ(parameter: _, body):
                return body.substitute(argument, at: 0).evaluate(exceptBind: exceptBind)
            default:
                return .application(function: function, argument: argument.evaluate(exceptBind: exceptBind), representation: .normal)
            }
        case .variable(index: _): return self
        case let .intersection(name, type0, type1): return .intersection(
            name: name,
            type0: type0.evaluate(exceptBind: exceptBind),
            type1: type1.evaluate(exceptBind: exceptBind)
        )
        case
            .first(let term),
            .second(let term),
            .symmetry(let term),
            .reflexive(of: _, as: let term),
            .cast(
                proof: _,
                value0: _,
                value1: let term // TODO: consider renaming value1 to the value to cast
            ),
            .both(type: _, value0: let term, value1: _),
            .rewrite(
                name: _,
                type: _,
                proof: _,
                term: let term
            ):
            return term.evaluate(
                exceptBind: exceptBind
            )
        case let .equal(x, y): return .equal(x.evaluate(exceptBind: exceptBind), y.evaluate(exceptBind: exceptBind))

        case .reference(let ref):
            return ref.term.evaluate(exceptBind: exceptBind)
        }
    }

    public func substitute(_ substitution: Term, at depth: Int ) -> Term {
        switch self {
        case .type:
            return .type
        case let .function(parameter, returnType):
            let parameter = parameter.substitute(substitution, at: depth)
            var substitution = substitution
            substitution.shift(depth: 0, 1)
            return .function(parameter: parameter, returnType: returnType.substitute(substitution, at: depth + 1))
        case let .λ(parameter, body):
            var parameter = parameter.substitute(substitution, at: depth)
            var substitution = substitution
            substitution.shift(depth: 0, 1)
            return .λ(parameter: parameter, body: body.substitute(substitution, at: depth + 1))
        case let .application(function, argument, representation):
            return .application(function: function.substitute(substitution, at: depth), argument: argument.substitute(substitution, at: depth), representation: representation)
        case .variable(let index):
            if depth == index {
                // TODO: add erased substitution support
                return substitution
            } else if index > depth {
                return .variable(index: index - 1)
            } else {
                return self
            }
        case let .intersection(name, type0, type1):
            let type0 = type0.substitute(substitution, at: depth)
            var substitution = substitution
            substitution.shift(depth: 0, 1)
            let type1 =  type1.substitute(substitution, at: depth + 1)
            return .intersection(name: name, type0: type0, type1: type1)

        case let .both(type, value0, value1):
            return .both(type: type.substitute(substitution, at: depth), value0: value0.substitute(substitution, at: depth), value1: value1.substitute(substitution, at: depth))
        case .first(let viewed):
            return .first(viewed.substitute(substitution, at: depth))
        case .second(let viewed):
            return .second(viewed.substitute(substitution, at: depth))
        case let .equal(term0, term1):
            return .equal(term0.substitute(substitution, at: depth), term1.substitute(substitution, at: depth))
        case let .reflexive(of: value, as: erasure):
            return .reflexive(of: value.substitute(substitution, at: depth), as: erasure.substitute(substitution, at: depth))
        case .symmetry(let proof):
            return .symmetry(proof.substitute(substitution, at: depth))
        case let .rewrite(name, type, proof, term: value):

            let proof = proof.substitute(substitution, at: depth)
            let value = value.substitute(substitution, at: depth)
            var substitution = substitution
            substitution.shift(depth: 0, 1)
            let type = type.substitute(substitution, at: depth + 1)

            return .rewrite(name: name, type: type, proof: proof, term: value)
        case let .cast(proof, value0, value1):
            return .cast(
                proof: proof.substitute(substitution, at: depth),
                value0: value0.substitute(substitution, at: depth),
                value1: value1.substitute(substitution, at: depth)
            )
        case .reference(var ref):
            if ref.clos {
                return self
            } else {
                ref.term = ref.term.substitute(substitution, at: depth)
                return .reference(ref)
            }
        }
    }


    // deprecated
    fileprivate func check(in context: Context = .empty) -> Attempt<Term, TypeErrors>  {
        switch self {
        case .type:
            return .success(.type)
        case let .function(parameter, returnType):
            let typeAnnotation = parameter.type
            let attemptTypeOfParameterType = expecting(Term.type, from: parameter.type.check(in: context).map {term in term.evaluate(exceptBind: false)}, for: typeAnnotation, in: self)
            var context = context
            context.extend(name: parameter.name, term: typeAnnotation // TODO: consider distinguishing between when a variable's associated term is a type vs a term
            )
            let attemptTypeOfReturnType = expecting(Term.type, from: returnType.check(in: context).map{type in type.evaluate(exceptBind: false)}, for: returnType, in: self)
            return attemptTypeOfParameterType.zip(attemptTypeOfReturnType, using: { _, _ in .type })

        case let .λ(parameter, body):
            let attemptTypeOfParameterType = expecting(Term.type, from: parameter.type.check(in: context).map {term in term.evaluate(exceptBind: false)}, for: parameter.type, in: self)
            var context = context
            context.extend(name: parameter.name, term: parameter.type)
            let bodyType = body.check(in: context)

            return bodyType.zip(attemptTypeOfParameterType) { returnType, _ in .function(parameter: parameter, returnType: returnType)}
        case let .application(function, argument, representation):
            let attemptFunctionType = function.check(in: context).map{type in type.evaluate(exceptBind: true)}
            let attemptArgumentType = argument.check(in: context)

            return attemptFunctionType.flatMap { functionType in
                guard case let .function(parameter, returnType) = functionType else {
                    return .failure(TypeErrors(error: .nonfunctionApplication(nonfunction: function, argument: argument, context: context)))
                }

                guard parameter.representation == representation else {
                    return .failure(TypeErrors(error: TypeError.representationMismatch(expected: parameter.representation, actual: representation, in: self, given: context)))
                }

                return attemptArgumentType.flatMap { argumentType in

                    guard argumentType.evaluate(exceptBind: false) == parameter.type.evaluate(exceptBind: false) else {
                        return .failure(TypeErrors(error: TypeError.invalidArgument(function: function, argument: argument, expected: parameter.type, actual: argumentType, given: context)))
                    }
                    guard case (.success(_), .success(_)) = (attemptFunctionType, attemptArgumentType) else {
                        return .failure(TypeErrors(error: .cannotDetermineType(for: self)))
                    }
                    return .success( returnType.substitute(argument, at: 0))
                }
            }
        case let .intersection(name, type0, type1):
            let attemptTypeOfType0 = expecting(Term.type, from: type0.check(in: context).map {term in term.evaluate(exceptBind: false)}, for: type0, in: self)
            var context = context
            context.extend(name: name, term: type0)
            let attemptTypeOfType1 = expecting(Term.type, from: type1.check(in: context).map { term in term.evaluate(exceptBind: false)}, for: type1, in: self)
            return attemptTypeOfType0.zip(attemptTypeOfType1) { _, _ in Term.type }
        case let .both(type, value0, value1):
            let originalType = type
            let originalValue1 = value1
            let type = type.evaluate(exceptBind: false)
            guard case let .intersection(name, type0: expectedType0, type1: expectedType1) = type else {
                return .failure(TypeErrors(error: .invalidBothType(in: self, given: context)))
            }

            let value0DisplayType: Attempt<Term, TypeErrors> = value0.check(in: context)
            let attemptValue0ActualType = value0DisplayType.map {value0TypeTerm in
                value0TypeTerm.evaluate(exceptBind: false)
            }

            let value1DisplayType: Attempt<Term, TypeErrors> = value1.check(in: context)
            let attemptValue1ActualType = value1DisplayType.map {value1TypeTerm in value1TypeTerm.evaluate(exceptBind: false)}
            let originalValue0 = value0
            let value0 = value0.evaluate(exceptBind: false)
            let value1 = value1.evaluate(exceptBind: false)
            let attemptValue = value0 == value1 ? Attempt.success(value0) : Attempt.partial(expected: value0, error: TypeErrors(error: .unequalViews(of: type, view0: value0, view1: value1, given: context)))

            let attemptFirstValueTypeChecks = attemptValue0ActualType.zip(attemptValue1ActualType).flatMap {viewsActualTypes in viewsActualTypes.0 == expectedType0.evaluate(exceptBind: false) ? .success(viewsActualTypes.1) : .failure(TypeErrors(error: .typeMismatch(expected: expectedType0, actual: value0DisplayType.expected ?? viewsActualTypes.0, for: originalValue0, in: self)))}

            return attemptFirstValueTypeChecks.zip(attemptValue).flatMap {tuple in
                let (actualType, valueToSubstitute) = tuple
                guard case .success(_) = attemptFirstValueTypeChecks else {
                    return .partial(expected: type, error: TypeErrors(error: .substitutionFailed(in: expectedType1, of: valueToSubstitute, dueTo: attemptFirstValueTypeChecks.error, given: context)))
                }
                let expectedType1 = expectedType1.substitute(valueToSubstitute, at: 0)
                guard actualType == expectedType1.evaluate(exceptBind: false) else {
                    return .partial(expected: type, error: TypeErrors(error: .typeMismatch(expected: expectedType1, actual: value1DisplayType.expected ?? actualType, for: originalValue1, in: self)))
                }

                return .success(type)
            }
        case .first(let term):
            let termType = term.check(in: context).map {termTypeTerm in termTypeTerm.evaluate(exceptBind: true)}
            return termType.flatMap { termType in
                guard case let .intersection(name, type0, type1) = termType.evaluate(exceptBind: false) else {
                    return .failure(TypeErrors(error: .nonIntersectionView(nonintersection: term, given: context)))
                }
                return .success(type0)

            }
        case .second(let term):
            let attemptTermType = term.check(in: context).map {termTypeTerm in termTypeTerm.evaluate(exceptBind: true)}
            return attemptTermType.flatMap { termType in
                guard case let .intersection(name, type0, type1) = self else {
                    return .failure(TypeErrors(error: .nonIntersectionView(nonintersection: term, given: context)))
                }

                guard case .success(_) = attemptTermType else {
                    return .failure(TypeErrors(error: .substitutionFailed(in: type1, of: term, dueTo: attemptTermType.error, given: context)))
                }

                return .success(type1.substitute(term, at: 0))

            }
        case .equal(_, _): return .success(.type)
        case .reflexive(of: let term, as: _):
            return .success(.equal(term, term))
        case .symmetry(let proof):
            return proof.check(in: context).map { proofType in proofType.evaluate(exceptBind: true) }.flatMap { proofType in
                guard case .equal(let term0, let term1) = proofType else {
                    return .failure(.init(error: .nonequalitySymmetry(nonequality: proof)))
                }

                return .success(Term.equal(term1, term0))
            }
        case let .rewrite(name, type, proof, term):
            let attemptCheckProof: Attempt<(Term, Term), _> = proof.check(in: context).map { proofType in proofType.evaluate(exceptBind: true) }.flatMap { proofType in
                guard case .equal(let term0, let term1) = proofType else {
                    return .failure(TypeErrors(error: .nonequalityRewrite(nonequality: proof, given: context)))
                }
                return .success((term0, term1))
            }
            let termTypeActual = term.check(in: context)
            return attemptCheckProof.zip(termTypeActual) {equatedTerms, termTypeActual in (expected: type.substitute(equatedTerms.0, at: 0), actual: termTypeActual, equatedTerms: equatedTerms)}.flatMap { terms in
                guard terms.0.evaluate(exceptBind: false) == terms.1.evaluate(exceptBind: false) else {
                    return .failure(TypeErrors(error: .typeMismatch(expected: terms.0, actual: terms.1, for: term, in: self)))
                }

                guard case .success(_) = attemptCheckProof else {
                    return .failure(TypeErrors(error: .invalidEqualityProof(proof: proof, given: context)))
                }


                return .success(type.substitute(terms.2.1, at: 0))
            }
        case let .cast(proof, value0, value1):
            let proofType = proof.check(in: context)
            guard case .success(.equal(_, _)) = proofType else {
                let newError = TypeErrors(error: .nonequalityCast(nonequality: proof, given: context))
                if let errors = proofType.error {
                    return .failure(errors ⋅ newError)
                } else {
                    return .failure(newError)
                }
            }
            return value0.check(in: context)

        case .variable(index: let index):
            return .success(context.type(of: index))
        case .reference(let ref):
            return ref.check(in: context)
        }
    }


    /// Returns whether the first term is a subtype of the second term.
    ///
    /// - Parameters:
    ///   - potentialSubtype: The term that may be a subtype.
    ///   - potentialSuperType: The term that may be a supertype.
    /// - Returns: Whether the first term is a subtype of the second term.
    public static func ⊆(_ potentialSubtype: Term, _ potentialSuperType: Term) -> Bool {
        switch (potentialSubtype, potentialSuperType) {
        case (.type, .type):
            // Type is a subtype of itself.
            return true

        // Intersection type subtyping rules:
        //
        // 1. T ⊆ A     T ⊆ B
        //    ---------------
        //       T ⊆ A ∩ B
        //
        // 2.   A ⊆ T
        //    ---------
        //    A ∩ B ⊆ T
        //
        // 3.   B ⊆ T
        //    ---------
        //    A ∩ B ⊆ T
        //
        // from: https://docs.scala-lang.org/scala3/reference/new-types/intersection-types-spec.html
        // foo : ⟨y : A⟩ B y

        // ⟨y : A⟩ B y ⊆ ⟨x : C⟩ D x
        // A ∩ B ⊆ C ∩ D
        case let (.intersection(name: name0, type0: subtype0, type1: subtype1), .intersection(name: name1, type0: supertype0, type1: supertype1)):
            // TODO: SHIFT. The variables need to be shifted to match
            return (potentialSubtype ⊆ supertype0 && potentialSubtype.shifted(depth: 0, 1) ⊆ supertype1) ||
                (subtype0 ⊆ potentialSuperType) ||
                (subtype1 ⊆ potentialSuperType.shifted(depth: 0, 1))
        case let (.intersection(name, type0: subtype0, type1: subtype1), potentialSuperType):
            // TODO: shift appropriately or expand the recursive call to properly handle the fact that intersections can be dependent
            return subtype0 ⊆ potentialSuperType || subtype1 ⊆ potentialSuperType.shifted(depth: 0, 1)
        case let (potentialSubtype, .intersection(name, type0: supertype0, type1: supertype1)):
            return potentialSubtype ⊆ supertype0 && potentialSubtype.shifted(depth: 0, 1) ⊆ supertype1

        case let (.reference(ref), other):
            // If the subtype is a reference, then the subtype is a subtype of the supertype if the term of the reference is a subtype of the supertype.
            return ref.term ⊆ other

        case let (other, .reference(ref)):
            // If the supertype is a reference, then the subtype is a subtype of the supertype if the subtype is a subtype of the term of the reference.
            return other ⊆ ref.term

        case let (.function(parameter: potentialSubtypeParameter, returnType: potentialSubtypeReturnType),
                  .function(parameter: potentialSuperTypeParameter, returnType: potentialSuperTypeReturnType)):
            switch (potentialSubtypeParameter.representation, potentialSuperTypeParameter.representation) {
            case (.normal, .normal), (.erased, .erased):
                return
                    potentialSuperTypeParameter.type ⊆ potentialSubtypeParameter.type &&
                    potentialSubtypeReturnType ⊆ potentialSuperTypeReturnType
            case (.erased, .normal), (.normal, .erased):
                // TODO: implement subtyping such that it takes into account generics with erased arguments
                // i.e. it should recognize when one type is a generalization of another type.
                return false

            }
        case let (.variable(index: index0), .variable(index: index1)):
            return index0 == index1
        case let (.symmetry(proof), other):
            return proof ⊆ other
        case let (other, .symmetry(proof)):
            return other ⊆ proof
        case
            let (.first(term), other),
            let (term, .first(other)),
            let (.second(term), other),
            let (term, .second(other)),
            let (.reflexive(of: _, as: term), other),
            let (term, .reflexive(of: _, as: other)),
            let (.rewrite(name: _, type: _, proof: _, term: term), other),
            let (term, .rewrite(name: _, type: _, proof: _, term: other)),
            let (.cast(proof: _, value0: _, value1: term), other),
            let (term, .cast(proof: _, value0: _, value1: other)),
            let (.both(type: _, value0: term, value1: _), other),
            let (term, .both(type: _, value0: other, value1: _)):
            return term ⊆ other
        case let (.equal(value0, value1), .equal(otherValue0, otherValue1)):
            return value0 == otherValue0 && value1 == otherValue1

        case let (.application(function, argument, representation), .application(function: otherFunction, argument: otherArgument, representation: otherRepresentation)):
            return representation == otherRepresentation && function == otherFunction && argument == otherArgument

        case let (.λ(parameter, body), .λ(parameter: otherParameter, body: otherBody)):
            return parameter.representation == otherParameter.representation && body == otherBody
        case
            (.application(function: _, argument: _, representation: _), .type),
            (.λ(parameter: _, body: _), .type),
            (.application(function: _, argument: _, representation: _), .variable(index: _)),
            (.λ(parameter: _, body: _), .variable(index: _)),
            (.λ(parameter: _, body: _), .application(function: _, argument: _, representation: _)),
            (.application(function: _, argument: _, representation: _), .function(parameter: _, returnType: _)),
            (.λ(parameter: _, body: _), .function(parameter: _, returnType: _)),
            (.application(function: _, argument: _, representation: _), .λ(parameter: _, body: _)),
            (.application(function: _, argument: _, representation: _), .equal(_, _)),
            (.λ(parameter: _, body: _), .equal(_, _)),
            (.equal(_, _), .type),
            (.equal(_, _), .variable(index: _)),
            (.equal(_, _), .application(function: _, argument: _, representation: _)),
            (.equal(_, _), .function(parameter: _, returnType: _)),
            (.equal(_, _), .λ(parameter: _, body: _)),
            (.variable(index: _), .type),
            (.variable(index: _), .application(function: _, argument: _, representation: _)),
            (.variable(index: _), .function(parameter: _, returnType: _)),
            (.variable(index: _), .λ(parameter: _, body: _)),
            (.variable(index: _), .equal(_, _)),
            (.function(parameter: _, returnType: _), .type),
            (.function(parameter: _, returnType: _), .variable(index: _)),
            (.function(parameter: _, returnType: _), .application(function: _, argument: _, representation: _)),
            (.function(parameter: _, returnType: _), .λ(parameter: _, body: _)),
            (.function(parameter: _, returnType: _), .equal(_, _)),
            (.type, .variable(index: _)),
            (.type, .application(function: _, argument: _, representation: _)),
            (.type, .function(parameter: _, returnType: _)),
            (.type, .λ(parameter: _, body: _)),
            (.type, .equal(_, _)):
            return false
        }
    }

    /// Determines the type of a term in a given context, or produces an error if the term is ill-typed.
    ///
    /// - Parameters:
    ///   - self: The term to type-check.
    ///   - context: The context in which to type-check the term.
    /// - Returns: The type of the term, or an error if the term is ill-typed.
    public func infer(in context: Context) -> Attempt<Term, TypeErrors> {
        switch self {
        case .variable(index: let index):
            // If the term is a variable, return the type of the variable from the context.
            return .success(context.type(of: index))

        case.type: return .success(.type)

        case let .function(parameter, returnType):
            // If the term is a function, check that the parameter and return types are types, and extend the context with the parameter.
            return parameter.type.check(is: .type, in: context).flatMap {
                var context = context
                context.extend(name: parameter.name, term: parameter.type)
                return returnType.check(is: .type, in: context)
            }.map { .type }

        case let .application(function, argument, representation):
            // If the term is an application, synthesize the type of the function and check that the argument
            // type matches the function parameter type.
            return function.infer(in: context).flatMap { type in
                let type = type.evaluate(exceptBind: true)
                guard case let .function(parameter, returnType) = type else {
                    return Attempt<(Parameter, Term), _>.failure(TypeErrors(error: .nonfunctionApplication(nonfunction: function, argument: argument, context: context)))
                }

                guard parameter.representation == representation else {
                    return Attempt.partial(expected: (parameter, returnType), error: TypeErrors(error: .representationMismatch(expected: parameter.representation, actual: representation, in: self, given: context)))
                }
                return Attempt.success((parameter, returnType))
            }.flatMap {functionTypeInfo in
                let parameter: Parameter = functionTypeInfo.0
                let returnType: Term = functionTypeInfo.1
                return argument.check(is: parameter.type.evaluate(exceptBind: false), in: context).flatMap {
                    return .success(returnType.substitute(argument, at: 0))
                }
            }

        case let .intersection(name, type0, type1):
            // If the term is an intersection, check that the type0 and type1 are types, and return .type
            return type0.check(is: .type, in: context).flatMap {
                var context = context
                context.extend(name: name, term: type0)
                return type1.check(is: .type, in: context)
            }.attach(.type)

        case let .both(type, value0, value1):
            // If the term is a both, check that the type is an intersection, and that the values are equal.
            let type = type.evaluate(exceptBind: false)
            guard case let .intersection(name: _, type0: expectedType0, type1: expectedType1) = type else {
                return .failure(TypeErrors(error: .invalidBothType(in: self, given: context)))
            }

            return value0.check(is: expectedType0, in: context).flatMap {
                let value0 = value0.evaluate(exceptBind: false)
                return value1.check(is: expectedType1.substitute(value0, at: 0).evaluate(exceptBind: false), in: context).zip(returning: value0.evaluate(exceptBind: false) == value1.evaluate(exceptBind: false) ? .success(()) : .failure(TypeErrors(error: .unequalViews(of: type, view0: value0, view1: value1, given: context))))
            }.attach(type)

        case let .first(term):
            // If the term is a first, check that the term is an intersection, and return the first type.
            let type = term.infer(in: context).map {termTypeTerm in termTypeTerm.evaluate(exceptBind: true)}
            return type.flatMap { type in
                guard case .intersection(_, _, _) = type.evaluate(exceptBind: false), case .intersection(_, let type0, _) = type else {
                    return .failure(TypeErrors(error: .nonIntersectionView(nonintersection: term, given: context)))
                }
                return .success(type0)
            }

        case let .second(term):
            // If the term is a second, check that the term is an intersection, and return the second type with the term substituted in.
            let attemptTermType = term.infer(in: context).map {termTypeTerm in termTypeTerm.evaluate(exceptBind: true)}
            return attemptTermType.flatMap { type in
                guard case .intersection(_, _, _) = type.evaluate(exceptBind: false), case .intersection(_, _, let type1) = type else {
                    return .failure(TypeErrors(error: .nonIntersectionView(nonintersection: term, given: context)))
                }

                guard case .success(_) = attemptTermType else {
                    return .failure(TypeErrors(error: .substitutionFailed(in: type1, of: term, dueTo: attemptTermType.error, given: context)))
                }

                return .success(type1.substitute(term, at: 0))
            }

        case .equal(_, _):
            // If the term is an equality, return .type
            return .success(.type)

        case .reflexive(of: let term, as: _):
            // If the term is a reflexive, return the equality type.
            return .success(.equal(term, term))

        case .symmetry(let proof):
            // If the term is a symmetry, check that the proof is an equality, and return the equality type with the terms swapped.
            return proof.infer(in: context).map {proofType in proofType.evaluate(exceptBind: true)}.flatMap { proofType in
                guard case .equal(let term0, let term1) = proofType else {
                    return .failure(TypeErrors(error: .nonequalitySymmetry(nonequality: proof)))
                }
                return .success(.equal(term1, term0))
            }

        case let .rewrite(name: _, type, proof, term):
            // If the term is a rewrite, check that the proof is an equality, and that the term has the correct type
            return proof.infer(in: context).map {proofType in proofType.evaluate(exceptBind: true) }.flatMap { proofType in
                guard case .equal(let equatedTerm0, let equatedTerm1) = proofType else {
                    return .failure(TypeErrors(error: .nonequalityRewrite(nonequality: proof, given: context)))
                }
                return term.check(is: type.substitute(equatedTerm0, at: 0).evaluate(exceptBind: false), in: context).map { type.substitute(equatedTerm1, at: 0) }
            }

        case let .cast(proof, value0, value1):
            // If the term is a cast, check that the proof is an equality, and that the values are equal.
            return proof.check(is: .equal(value1, value0), in:context).zip(returning: value0.infer(in: context))

        case .λ(parameter: let parameter, body: let body):
            // If the term is a lambda, check that the parameter is a type, and synthesize the body.
            return parameter.type.check(is: .type, in: context).flatMap {
                var context = context
                context.extend(name: parameter.name, term: parameter.type)
                return body.infer(in: context).map {returnType in .function(parameter: parameter, returnType: returnType)}
            }

        case .reference(let ref):
            // If the term is a reference, synthesize the referenced term.
            return ref.infer(in: context)
        }
    }

    // Bidirectional type checking reference:
    // https://davidchristiansen.dk/tutorials/implementing-types-hs.pdf

    /// Check if the term is of a certain type.
    ///
    /// - Parameters:
    ///   - type: The type to check against. The type should be fully evaluated before calling this function.
    ///   - context: The context to check in.
    /// - Returns: A success if the term is of the given type, or a failure with the type errors.
    public func check(is type: Term/* Should be fully evaluated*/, in context: Context) -> Attempt<Void, TypeErrors> {
        switch self {

        case .type:
            // If the term is a type, check that the `type` is a type.
            guard .type ⊆ type else {
                return .failure(TypeErrors(error: .typeMismatch(expected: type, actual: .type, for: self, in: self)))
            }
            return .success(())

        case let .function(parameter, returnType):
            // If the term is a function, check that the parameter is a type, and check that the
            // return type is a type.
            return parameter.type.check(is: .type, in: context).flatMap {
                var context = context
                context.extend(name: parameter.name, term: parameter.type)
                return returnType.check(is: .type, in: context)
            }.flatMap {
                guard case .type = type else {
                    return .failure(TypeErrors(error: .typeMismatch(expected: type, actual: .type, for: self, in: self)))
                }
                return .success(())
            }
        case let .intersection(name: _, type0, type1):
            // If the term is an intersection, check that the type0 and type1 are types.
            return type0.check(is: .type, in: context).flatMap {
                type1.check(is: .type, in: context)
            }.flatMap {
                guard case .type = type else {
                    return .failure(TypeErrors(error: .typeMismatch(expected: type, actual: .type, for: self, in: self)))
                }
                return .success(())
            }
        case let .λ(parameter, body):
            switch type {
            case let .function(parameter: parameterSpecifiedInType, returnType: returnTypeSpecifiedInType):
                // Contravariance for Parameters:
                //
                // When checking a function type, the parameter type of the function being checked should be a supertype of the parameter type specified in the
                // expected function type. This is because if a function is expected to accept a broader range of input types, any function that accepts a narrower
                // range of inputs should also be acceptable.
                //
                // Covariance for Return Types:
                //
                // The return type of the function being checked should be a subtype of the return type specified in the expected function type. This is because if a
                // function is expected to return a certain type, it should be acceptable if it returns a more specific type.

                guard parameterSpecifiedInType.type ⊆ parameter.type else {
                    return .failure(TypeErrors(error: .typeMismatch(expected: parameterSpecifiedInType.type, actual: parameter.type, for: self, in: self)))
                }
                var context = context
                context.extend(name: parameter.name, term: parameter.type)
                return body.check(is: returnTypeSpecifiedInType, in: context)
            default:
                // If the type is not a function, return a type mismatch error.
                // Scaffolding for future error handling.
                return self.infer(in: context).map { type in type.evaluate(exceptBind: false) }.flatMap { actualType in
                    guard actualType ⊆ type else {
                        return .failure(TypeErrors(error: .typeMismatch(expected: type, actual: actualType, for: self, in: self)))
                    }
                    return .success(())
                }
            }

        case let .both(typeAnnotation, value0, value1):
            // If the term is a both, check that the type annotation is an intersection, and that the values are equal.
            return typeAnnotation.check(is: .type, in: context).flatMap {
                let type = typeAnnotation.evaluate(exceptBind: false)
                guard case let .intersection(_, expectedType0, type1: expectedType1) = type else {
                    return .failure(TypeErrors(error: .invalidBothType(in: self, given: context)))
                }
                return value0.check(is: expectedType0, in: context).flatMap {
                    let expectedType1: Term = expectedType1.substitute(value0, at: 0).evaluate(exceptBind: false)
                    return value1.check(is: expectedType1, in: context).zip(returning: value0.evaluate(exceptBind: false) == value1.evaluate(exceptBind: false) ? .success(()) : .failure(TypeErrors(error: .unequalViews(of: type, view0: value0, view1: value1, given: context))))
                        .map {_ in (expectedType0, expectedType1)}
                }.flatMap { actualTypes in
                    if typeAnnotation ⊆ type {
                        return .success(())
                    }

                    if actualTypes.0 ⊆ type || actualTypes.1 ⊆ type {
                        return .success(())
                    }

                    return .failure(TypeErrors(error: .typeMismatch(expected: type, actual: typeAnnotation, for: self, in: self)))
                }

            }

        case .equal(_, _):
            // If the term is an equality, check that the `type` is a type.
            guard case .type = type else {
                return .failure(TypeErrors(error: .typeMismatch(expected: type, actual: .type, for: self, in: self)))
            }
            return .success(())
        case .first(_), .second(_), .variable(index: _), .rewrite(name: _, type: _, proof: _, term: _), .cast(proof: _, value0: _, value1: _), .symmetry(_), .reflexive(of: _, as: _), .application(function: _, argument: _, representation: _):
            // Fallback to inferring the type of the term and checking that it is subtype of the expected type.
            return self.infer(in: context).map {type in type.evaluate(exceptBind: false)}.flatMap { actualType in actualType ⊆ type ? .success(()) : .failure(TypeErrors(error: .typeMismatch(expected: type, actual: actualType, for: self, in: self))) }

        case .reference(let ref):
            // If the term is a reference, check that the referenced term has the expected type.
            return ref.check(is: type, in: context)
        }
    }

    // TODO: Update for the new syntax
    // depricated
    public func code(in context: Context) -> String {
        switch self {
        case .type:
            return "Type"

        case let .function(parameter, returnType):
            let quantifier = switch parameter.representation { case .erased: "∀" case .normal: "∏" }

            let typeAnnotation = parameter.type.code(in: context)
            var context = context
            context.extend(name: parameter.name, term: parameter.type)

            return "\(quantifier) \(parameter.name) : \(typeAnnotation) → \(returnType.code(in: context))"


        case let .λ(parameter, body):
            let lambda = switch parameter.representation { case .erased: "Λ" case .normal: "λ" }

            let typeAnnotation = parameter.type.code(in: context)
            var context = context
            context.extend(name: parameter.name, term: parameter.type)
            return "\(lambda) \(parameter.name) : \(typeAnnotation). \(body.code(in: context))"


        case let .application(function, argument, representation: .normal):
            return "\(function.code(in: context)) (\(argument.code(in: context))"
        case let .application(function, argument, representation: .erased):
            return "\(function.code(in: context)) ~(\(argument.code(in: context))"

        case let .intersection(name, type0, type1):
            let type0Annotation = type0.code(in: context)
            var context = context
            context.extend(name: name, term: type0)
            return "⟨\(name) : \(type0Annotation)⟩ \(type1.code(in: context))"

        case let .both(type, value0, value1):
            return "{\(value0.code(in: context)), \(value1.code(in: context))} ∈ \(type.code(in: context))"

        case let .reflexive(of: value, as: realizer):
            return "𝐫𝐞𝐟𝐥 \(value.code(in: context)) 𝐚𝐬 \(realizer.code(in: context))"

        case let .variable(index):
            return context.name(at: index) ?? "#\(index)"
        case let .symmetry(proof):
            return "𝐬𝐲𝐦 \(proof.code(in: context))"
        case let .first(value):
            return "⓿ \(value.code(in: context))"
        case let .second(value):
            return "❶ \(value.code(in: context))"

        case let .equal(x, y):
            return "|\(x.code(in: context)) = \(y.code(in: context))|"
        case let .cast(proof, value0, value1):
            return "𝐜𝐚𝐬𝐭 \(value0.code(in: context)) 𝐭𝐨 𝐭𝐲𝐩𝐞 𝐨𝐟 \(value1.code(in: context)) 𝐮𝐬𝐢𝐧𝐠 \(proof.code(in: context))"
        case let .rewrite(name, type, proof, term):
            return "𝐮𝐬𝐢𝐧𝐠 \(proof.code(in: context)) 𝐫𝐞𝐰𝐫𝐢𝐭𝐞 \(name) 𝐢𝐧 \(type.code(in: context)) ∋ \(term.code(in: context))"
        case .reference(_):
            fatalError("TODO: not implemented yet")
        }

    }
}

/// Parses an ASCII identifier.
let identifier = Parser.skippedSubstring(
    by: Parser.tuple(
        Parser.asciiLetter,
        Parser.many(Parser.one(of: [Parser.asciiLetter, Parser.decimalDigit, Parser.character("_")]))
    )
) <?> "identifier"

// depricated
let representationFunctionParser = Parser.one(
    of: [ Parser.substring(
        "∀"
    ).map{
        _ in Representation.erased
    },
          Parser.substring(
            "∏"
          ).map {
              _ in Representation.normal
          } ]
)

/// Parses the representation of a lambda's parameter.
let representationLambdaParser = Parser.one(of: [Parser.substring("λ").map{_ in Representation.normal}, Parser.substring("Λ").map{_ in Representation.erased}])

/// Single space or newline parser.
let space = Parser.space <|> Parser.newline <?> "single space"

/// Multiple spaces or newlines parser.
let spaces = Parser.skip(Parser.many(space)) <?> "spaces allowed"

/// Multiple spaces or newlines parser with at least one space.
let spaces1 = Parser.skip(Parser.many(space, minCount: 1)) <?> "one or more spaces"

/// Parses a return type of a function where the return type can depend on the parameter.
fileprivate func returnTypeParser(representation: Representation, name: String, type: Term) -> Parser<Term> {

    return Parser { originalState in

        var state = originalState
        let originalContext = state.userInfo[Context.self]

        // Extend the context with the parameter.
        state.userInfo[Context.self].extend(
            name: name
        )

        // Parse the return type.
        let result = termParser.parse(
            &state
        )

        // Restore the original context.
        state.userInfo[Context.self] = originalContext

        return ParserReply(result: result.map{
            returnType in Term.function(
                parameter: Parameter(
                    name: name,
                    type: type,
                    representation: representation
                ),
                returnType: returnType
            )
        },
                           state: state)
    }
}

/// Parses a lambda body and returns a lambda term.
fileprivate func lambdaBodyParser(representation: Representation, name: String, type: Term, term: Term? = nil) -> Parser<Term> {
    return Parser { originalState in

        // TODO: This code is duplicated in the returnTypeParser function. Refactor it.
        var state = originalState
        let originalContext = state.userInfo[Context.self]
        state.userInfo[Context.self].extend(
            name: name, term: term
        )
        let result = termParser.parse(
            &state
        )
        state.userInfo[Context.self] = originalContext

        return ParserReply(result: result.map{
            body in Term.λ(
                parameter: Parameter(
                    name: name,
                    type: type,
                    representation: representation
                ),
                body: body
            )
        },
                           state: state)
    } <!> "lambda body"
}

/// Parses a bound variable.
let boundVariable : Parser<Term> = identifier.flatMap {name in Parser{ state in

    // Check if the variable is defined in the context.
    // If it is, return the variable term.
    guard let variable = state.userInfo[Context.self][name, skipping: 0] else {
        return ParserReply(
            result: .failure(
                [ParseError.generic(
                    message: "\(name) not defined in scope"
                )]
            ),
            state: state
        )
    }
    // TODO: consider using the term associated with the variable in the context
    return ParserReply(
        result: .success(
            variable.term,
            []
        ),
        state: state
    )
}} <?> "bound variable"

/// Parse a term.
func termParserBuilder(_ termParser: Parser<Term>) -> Parser<Term> {
    // Parse a lambda term.
    // Example: λ x : A. B x
    // Example: Λ x : A. B x
    let lambda = Parser.tuple(
        representationLambdaParser <* spaces,
        identifier <* spaces,
        Parser.skip(
            Parser.character(
                ":"
            )
        ) <* spaces,
        termParser <* Parser.skip(
            Parser.character(
                "."
            )
        ) <* spaces
    ).flatMap {
        lambdaParameter in lambdaBodyParser(
            representation: lambdaParameter.0,
            name: String(
                lambdaParameter.1
            ),
            type: lambdaParameter.3
        )
    } <?> "Lambda term"

    // Bound variable or parenthesized term.
    // Example: x
    // Example: (f x)
    let boundVariableOrParenthesizedTerm = boundVariable <|> (
        Parser.character(
            "("
        ) *> spaces *> termParser <* spaces <* Parser.character(
            ")"
        )
    )

    // Function argument.
    // Example: x
    // Example: {x}
    // Example: (f x)
    let functionArgument = boundVariableOrParenthesizedTerm.map {
        argument in (
            argument: argument,
            representation: Representation.normal
        )
    } <|> (
        Parser.character(
            "{"
        ) *> spaces *> termParser <* spaces <* Parser.character(
            "}"
        )
    ).map {
        argument in (
            argument: argument,
            representation: Representation.erased
        )
    } <?> "function argument"

    // Function application.
    // Example: f x y
    // Example: g {x} y
    let application: Parser<Term> = Parser.attempt(Parser.tuple(
        boundVariableOrParenthesizedTerm <* spaces1,
        Parser.many(
            functionArgument,
            separatedBy: spaces1,
            allowEndBySeparator: true,
            minCount: 1
        )
    )).map {
        app in Term.application(
            function: app.0,
            arguments: app.1
        )
    } <!> "function application term"

    // Parse a let binding.
    // Example: 𝐥𝐞𝐭 x : A = t 𝐢𝐧 u
    // Note that keywords are defined using unicode bold characters.
    let letParser = Parser.tuple(
        Parser.substring(
            "𝐥𝐞𝐭"
        ) *> spaces1 *> identifier ,  spaces <*  Parser.character(
            "="
        ) <*  spaces,
        termParser <* spaces1 <* Parser.substring(
            "𝐢𝐧"
        ) <* spaces1
    ).flatMap { binding in Parser { originalState in

        var state = originalState
        let originalContext = state.userInfo[Context.self]
        let name = String(
            binding.0
        )
        state.userInfo[Context.self].extend(
            name: name,
            term: .reference(Reference(
                name: name,
                term: binding.2,
                clos: false
            ))
        )
        let result = termParser.parse(
            &state
        )
        state.userInfo[Context.self] = originalContext

        return ParserReply(result: result.map{
            body in
            var body = body
            body.shift(
                depth: 0,
                -1
            )
            return body
        }, state: state)
    }

    } <?> "let binding"

    // Parse a value of dependent intersection type.
    // Note that a dependent intersection type is a intersection where the second type
    // depends on the value interpreted as the first type. The erased function type is different
    // Example: {x, y} ∈ t
    let both = Parser.attempt(
        Parser.tuple(
            Parser.character(
                "{"
            ) *> spaces *> termParser <* spaces <* Parser.character(
                ","
            ) <* spaces,
            termParser <* spaces <* Parser.character(
                "}"
            ) <* spaces <* Parser.character(
                "∈"
            ) <* spaces,
            termParser
        )
    ).map {
        bothContents in Term.both(
            type: bothContents.2,
            value0: bothContents.0,
            value1: bothContents.1
        )
    }

    // Parse a dependent intersection type.
    // Example: ⟨x : A⟩ B x
    let intersection = Parser.tuple(
        Parser.character(
            "⟨"
        ) *> spaces *> identifier <* spaces <* Parser.character(
            ":"
        ) <* spaces,
        termParser <* spaces <* Parser.character(
            "⟩"
        ) <* spaces,
        termParser
    ).map {
        intersectionContents in Term.intersection(
            name: String(
                intersectionContents.0
            ),
            type0: intersectionContents.1,
            type1: intersectionContents.2
        )
    } <?> "dependent intersection type"

    // Parse a propositional equality type.
    // Example: |x = y|
    let equalityType = Parser.tuple(
        (Parser.character(
            "|"
        ) <?> "opening equality type bar") *> spaces *> termParser <* spaces <* (Parser.character(
            "="
        ) <?> "equality type equal sign (=)") <* spaces,
        termParser <* spaces <* (Parser.character(
            "|"
        ) <!> "closing equality type bar")
    ).map {
        terms in Term.equal(
            terms.0,
            terms.1
        )
    } <!> "equality type"

    // Parse a proof of reflexivity.
    // Example: 𝐫𝐞𝐟𝐥 t 𝐚𝐬 u
    let reflexive = Parser.tuple(
        Parser.substring(
            "𝐫𝐞𝐟𝐥"
        ) *> spaces1 *> termParser <* spaces1 <* Parser.substring(
            "𝐚𝐬"
        ) <* spaces1,
        termParser
    ).map {
        proof in Term.reflexive(
            of: proof.0,
            as: proof.1
        )
    }

    // Parse symmetry unary operator on equality proofs.
    // Example: 𝐬𝐲𝐦 t
    let symmetry = (Parser.substring("𝐬𝐲𝐦") *> spaces1 *> termParser).map { proof in Term.symmetry(proof) }

    // Parse a usage of an equality proof to rewrite.
    // Example: 𝐮𝐬𝐢𝐧𝐠 t 𝐫𝐞𝐰𝐫𝐢𝐭𝐞 x 𝐢𝐧 P x ∋ y
    let rewrite = Parser.tuple(Parser.substring("𝐮𝐬𝐢𝐧𝐠") *> spaces1 *> termParser <* spaces1, Parser.substring("𝐫𝐞𝐰𝐫𝐢𝐭𝐞") *> spaces1 *> identifier <* spaces1 <* Parser.substring("𝐢𝐧") <* spaces1).flatMap { proofAndIdentifier in
        let proof = proofAndIdentifier.0
        let identifier = String(proofAndIdentifier.1)
        return Parser.tuple(Parser { originalState in
            var state = originalState
            let originalContext = state.userInfo[Context.self]
            state.userInfo[Context.self].extend(name: identifier)
            let type = termParser.parse(&state)
            state.userInfo[Context.self] = originalContext

            return ParserReply(result: type, state: state)
        }, spaces *> Parser.character("∋") *> spaces *> termParser).map { typeAndTerm in
            let type = typeAndTerm.0
            let term = typeAndTerm.1
            return Term.rewrite(name: identifier, type: type, proof: proof, term: term)
        }
    }

    // Parse a cast.
    // Example: 𝐜𝐚𝐬𝐭 t 𝐭𝐨 𝐭𝐲𝐩𝐞 𝐨𝐟 u 𝐮𝐬𝐢𝐧𝐠 v
    let cast = Parser.tuple(
        Parser.substring(
            "𝐜𝐚𝐬𝐭"
        ) *> spaces1 *> termParser <* spaces1 <* Parser.substring(
            "𝐭𝐨"
        ) <* spaces1 <* Parser.substring(
            "𝐭𝐲𝐩𝐞"
        ) <* spaces1 <* Parser.substring(
            "𝐨𝐟"
        ) <* spaces1,
        termParser <* spaces1 <* Parser.substring(
            "𝐮𝐬𝐢𝐧𝐠"
        ) <* spaces1,
        termParser
    ).map {
        castTermContents in Term.cast(
            proof: castTermContents.2,
            value0: castTermContents.1,
            value1: castTermContents.0
        )
    }

    // Parse parameter type.
    let parameterType = Parser.one(
        of: [
            Parser.substring(
                "Type"
            ).map {
                _ in Term.type
            },
            letParser,
            lambda,
            both,
            intersection,
            equalityType,
            reflexive,
            symmetry,
            rewrite,
            cast,
            Parser.not(identifier *> spaces *> Parser.character(":"), label: "dependent function type") *> (application <|> boundVariable),
            Parser.character("(") *> spaces *> termParser <* spaces <* Parser.character(")"),
        ]
    ) <?> "Parameter type"

    // Parse a normal dependent function type.
    // Example: x:A → B x
    let normalDependentFunctionType = Parser.attempt(Parser.tuple(
        Parser.discardSecond(
            identifier,
            spaces
        ),
        Parser.discardFirst(
            Parser.discardSecond(
                Parser.character(
                    ":"
                ),
                spaces
            ),
            parameterType
        ),

        Parser.discardFirst(
            Parser.discardFirst(
                spaces,
                Parser.substring(
                    "→"
                )
            ),
            spaces
        )

    )).flatMap { result in
        return returnTypeParser(representation: .normal, name: String(result.0), type: result.1)
    } <!> "explicit normal dependent function type"

    let nonDependentFunctionType = Parser.attempt(parameterType <* spaces <* Parser.character("→") <* spaces).flatMap { parameterType in
        returnTypeParser(representation: .normal, name: "", type: parameterType)
    } <!> "Non-dependent function type"

    // Parse an implicit erased dependent function type.
    // Example: ⋂ x : A. B x
    // The symbol `⋂` is used to represent an implicit function type.
    // In a future version, `∀` will be used to represent explicit erased function types.
    let implicitDependentFunctionType = Parser.tuple(
        Parser.discardSecond(
            Parser.skip(
                Parser.substring(
                    "⋂"
                )
            ),
            spaces
        ),
        Parser.discardSecond(
            identifier,
            spaces
        ),
        Parser.discardSecond(
            Parser.skip(
                Parser.character(
                    ":"
                )
            ),
            spaces
        ),
        termParser <* spaces <*
        Parser.skip(
            Parser.character(
                "."
            )
        ) <*
        spaces
    ).flatMap { result in
        returnTypeParser(representation: .erased, name: String(result.1), type: result.3)
    } <?> "implicit erased dependent function type"

    // Parse a function type of normal or erased representation.
    // Example: x:A → B x
    // Example: ⋂ x : A. B x
    let dependentFunctionType = Parser.one(
        of: [
            normalDependentFunctionType,
            implicitDependentFunctionType
        ]
    ) <!> "dependent function type"


    return  Parser.one(
        of: [
            Parser.substring(
                "Type"
            ).map {
                _ in Term.type
            },
            lambda,
            dependentFunctionType,
            letParser,
            both,
            intersection,
            equalityType,
            reflexive,
            symmetry,
            rewrite,
            cast,
            nonDependentFunctionType,
            application,
            Parser.character("(") *> spaces *> termParser <* spaces <* Parser.character(")"),
            boundVariable
        ]
    ) <?> "term"

}

// Parse a term.
let termParser = Parser.recursive(termParserBuilder)

extension Term: Hashable {

    /// Hashes the essential components of this term by feeding them into the given hasher.
    /// Note that names are not hashed, as they are not essential to the term.
    /// This means that two terms with different names but the same structure will have the same hash.
    /// This is important for the implementation of the `==` operator for terms to uphold the law:
    /// `x == y ==> x.hashValue == y.hashValue`
    ///
    /// - Parameter hasher: The hasher to use when combining the components of this term.
    /// - Complexity: O(n), where n is the number of nodes in the term.
    public func hash(into hasher: inout Hasher) {
        switch self {
        case let .application(function, argument, representation):
            hasher.combine(1)
            hasher.combine(function)
            hasher.combine(argument)
            hasher.combine(representation)
        case .type:
            hasher.combine(2)
        case let .variable(index):
            hasher.combine(3)
            hasher.combine(index)
        case let .function(parameter, returnType):
            hasher.combine(4)
            hasher.combine(parameter.representation)
            hasher.combine(parameter.type)
            hasher.combine(returnType)
        case let .λ(parameter, body):
            hasher.combine(5)
            hasher.combine(parameter.representation)
            hasher.combine(body)
        case let .intersection(name: _, type0, type1):
            hasher.combine(6)
            hasher.combine(type0)
            hasher.combine(type1)
        case let .both(type: _, value0, value1: _):
            value0.hash(into: &hasher)
        case let .first(term):
            term.hash(into: &hasher)
        case let .second(term):
            term.hash(into: &hasher)
        case let .equal(value0, value1):
            hasher.combine(10)
            hasher.combine(value0)
            hasher.combine(value1)
        case let .reflexive(of: _, as: erasedAs):
            erasedAs.hash(into: &hasher)
        case let .symmetry(proof):
            proof.hash(into: &hasher)
        case let .rewrite(name: _, type: _, proof: _, term):
            term.hash(into: &hasher)
        case let .cast(proof: _, value0: _, value1):
            value1.hash(into: &hasher)
        case let .reference(ref):
            ref.term.hash(into: &hasher)
        }
    }
}


extension Term: Equatable {

    /// Returns a Boolean value indicating whether two terms are equal.
    ///
    /// - Parameters:
    ///   - lhs: A term to compare.
    ///   - rhs: Another term to compare.
    /// - Returns: `true` if the terms are equal, otherwise `false`.
    /// - Complexity: O(n), where n is the number of nodes in the term.
    public static func ==(lhs: Self, rhs: Self) -> Bool {
        switch (lhs, rhs) {

        case let (.application(function, argument, representation), .application(function: function1, argument: argument1, representation: representation1)):
            return representation == representation1 && function == function1 && argument == argument1

        case (.type, .type):
            return true
        case let (.variable(index), .variable(index: otherIndex)):
            return index == otherIndex

        case let (.function(parameter, returnType), .function(parameter: parameter1, returnType: returnType1)):
            return parameter.representation == parameter1.representation && parameter.type == parameter1.type && returnType == returnType1

        case let (.λ(parameter, body), .λ(parameter: parameter1, body: body1)):
            return parameter.representation == parameter1.representation && body == body1

        case let (.intersection(name: _, type0, type1), .intersection(name: _, type0: otherType0, type1: otherType1)):
            return type0 == otherType0 && type1 == otherType1

        case let (.both(type: _, value0, value1: _), other):
            return value0 == other

        case let (other, .both(type: _, value0, value1: _)):
            return value0 == other

        case let (.first(term), other):
            return term == other

        case let (other, .first(term)):
            return term == other

        case let (.second(term), other):
            return term == other

        case let (other, .second(term)):
            return term == other

        case let (.equal(value0, value1), .equal(otherValue0, otherValue1)):
            return value0 == otherValue0 && value1 == otherValue1

        case let (.reflexive(of: _, as: erasedAs), other):
            return erasedAs == other

        case let (other, .reflexive(of: _, as: erasedAs)):
            return erasedAs == other

        case let (.symmetry(proof), other):
            return proof == other

        case let (other, .symmetry(proof)):
            return proof == other

        case let (.rewrite(name: _, type: _, proof: _, term), other):
            return term == other

        case let (other, .rewrite(name: _, type: _, proof: _, term)):
            return term == other

        case let (.cast(proof: _, value0: _, value1), other):
            return value1 == other

        case let (other, .cast(proof: _, value0: _, value1)):
            return value1 == other

        case let (.reference(ref), other):
            return ref.term == other

        case let (other, .reference(ref)):
            return ref.term == other

            // catch all cases for failure
        case (.equal(_, _), .type):
            fallthrough
        case (.equal(_, _), .variable(index: _)):
            fallthrough
        case (.equal(_, _), .application(function: _, argument: _, representation: _)):
            fallthrough
        case (.equal(_, _), .function(parameter: _, returnType: _)):
            fallthrough
        case (.equal(_, _), .λ(parameter: _, body: _)):
            fallthrough
        case (.equal(_, _), .intersection(name: _, type0: _, type1: _)):
            fallthrough

        case (.intersection(name: _, type0: _, type1: _), .type):
            fallthrough
        case (.intersection(name: _, type0: _, type1: _), .variable(index: _)):
            fallthrough
        case (.intersection(name: _, type0: _, type1: _), .application(function: _, argument: _, representation: _)):
            fallthrough
        case (.intersection(name: _, type0: _, type1: _), .function(parameter: _, returnType: _)):
            fallthrough
            //
        case (.intersection(name: _, type0: _, type1: _), .λ(parameter: _, body: _)):
            fallthrough

        case (.intersection(name: _, type0: _, type1: _), .equal(_, _)):
            fallthrough

        case (.λ(parameter: _, body: _), .type):
            fallthrough
        case (.λ(parameter: _, body: _), .variable(index: _)):
            fallthrough
        case (.λ(parameter: _, body: _), .application(function: _, argument: _, representation: _)):
            fallthrough
        case (.λ(parameter: _, body: _), .function(parameter: _, returnType: _)):
            fallthrough
        case (.λ(parameter: _, body: _), .intersection(name: _, type0: _, type1: _)):
            fallthrough

        case (.λ(parameter: _, body: _), .equal(_, _)):
            fallthrough
        case (.function(parameter: _, returnType: _), .type):
            fallthrough
        case (.function(parameter: _, returnType: _), .variable(index: _)):
            fallthrough
        case (.function(parameter: _, returnType: _), .application(function: _, argument: _, representation: _)):
            fallthrough
        case (.function(parameter: _, returnType: _), .λ(parameter: _, body: _)):
            fallthrough
        case (.function(parameter: _, returnType: _), .intersection(name: _, type0: _, type1: _)):
            fallthrough

        case (.function(parameter: _, returnType: _), .equal(_, _)):
            fallthrough

        case (.variable(index: _), .type):
            fallthrough
        case (.variable(index: _), .application(function: _, argument: _, representation: _)):
            fallthrough
        case (.variable(index: _), .function(parameter: _, returnType: _)):
            fallthrough
        case (.variable(index: _), .λ(parameter: _, body: _)):
            fallthrough
        case (.variable(index: _), .intersection(name: _, type0: _, type1: _)):
            fallthrough

        case (.type, .variable(index: _)):
            fallthrough
        case (.type, .application(function: _, argument: _, representation: _)):
            fallthrough
        case (.type, .function(parameter: _, returnType: _)):
            fallthrough
        case (.type, .λ(parameter: _, body: _)):
            fallthrough
        case (.type, .intersection(name: _, type0: _, type1: _)):
            fallthrough

        case (.application(function: _, argument: _, representation: _), .type):
            fallthrough
        case (.application(function: _, argument: _, representation: _), .variable(index: _)):
            fallthrough
        case (.application(function: _, argument: _, representation: _), .function(parameter: _, returnType: _)):
            fallthrough
        case (.application(function: _, argument: _, representation: _), .λ(parameter: _, body: _)):
            fallthrough
        case (.application(function: _, argument: _, representation: _), .intersection(name: _, type0: _, type1: _)):
            fallthrough

        case (.application(function: _, argument: _, representation: _), .equal(_, _)):
            fallthrough

        case (.variable(index: _), .equal(_, _)):
            fallthrough
        case (.type, .equal(_, _)):
            return false
        }
    }
}

// copied from: https://forums.swift.org/t/inout-variables-in-for-in-loops/61380/6
extension MutableCollection {

  /// Calls the given closure on each element in the collection in the same order as a `for-in` loop.
  /// Allows the closure to modify the element in-place.
  ///
  /// - Parameter modify: A closure that takes an element of the collection as a inout parameter.
  ///   If the closure has a return value, it is ignored.
  /// - Throws: Rethrows any error thrown by the closure.
  mutating func modifyEach(_ modify: (inout Element) throws -> Void) rethrows {
    var i = startIndex
    while i != endIndex {
      try modify(&self[i])
      formIndex(after: &i)
    }
  }
}

extension Variable {

    /// Shifts the variable by `inc` if the index is greater or equal to `depth`.
    /// - Parameters:
    ///   - depth: The depth to shift from.
    ///   - inc: The increment to shift by.
    /// - Returns: The shifted variable.
    mutating func shift(depth: Int, _ inc: Int) {
        term.shift(depth: depth, inc)
    }
}

extension Term {
    /// Parses a term from a string.
    /// - Parameter code: The string to parse.
    /// - Returns: The parsed term.
    static func parse(code: String) throws -> Term {
        try termParser.run(code)
    }

    /// Shifts the term by `inc` if the index is greater or equal to `depth` and returns
    /// the shifted term instead of mutating it.
    /// - Parameters:
    ///   - depth: The depth to shift from.
    ///   - inc: The increment to shift by.
    /// - Returns: The shifted term.
    func shifted(depth: Int, _ inc: Int) -> Term {
        var copy = self
        copy.shift(depth: depth, inc)
        return copy
    }

    /// Shifts the term by `inc` if the index is greater or equal to `depth` and mutates it.
    /// - Parameters:
    ///   - depth: The depth to shift from.
    ///   - inc: The increment to shift by.
    /// - Returns: The shifted term.
    mutating func shift(depth: Int, _ inc: Int) {
        switch self {
        case .type:
            return
        case var .function(parameter, returnType):
            parameter.type.shift(depth: depth, inc)
            returnType.shift(depth: depth + 1, inc)
            self = .function(parameter: parameter, returnType: returnType)
        case var .λ(parameter, body):
            parameter.type.shift(depth: depth, inc)
            body.shift(depth: depth + 1, inc)
            self = .λ(parameter: parameter, body: body)
        case var .application(function, argument, representation):
            function.shift(depth: depth, inc)
            argument.shift(depth: depth, inc)
            self = .application(function: function, argument: argument, representation: representation)
        case let .variable(index):
            if index < depth {
                self = .variable(index: index)
            } else {
                self = .variable(index: index + inc)
            }
        case var .intersection(name, type0, type1):
            type0.shift(depth: depth, inc)
            type1.shift(depth: depth + 1, inc)
            self = .intersection(name: name, type0: type0, type1: type1)
        case var .both(type, value0, value1):
            type.shift(depth: depth, inc)
            value0.shift(depth: depth, inc)
            value1.shift(depth: depth, inc)
            self = .both(type: type, value0: value0, value1: value1)
        case var .first(term):
            term.shift(depth: depth, inc)
            self = .first(term)
        case var .second(term):
            term.shift(depth: depth, inc)
            self = .second(term)
        case var .equal(x, y):
            x.shift(depth: depth, inc)
            y.shift(depth: depth, inc)
            self = .equal(x, y)
        case var .reflexive(of: value, as: erasure):
            value.shift(depth: depth, inc)
            erasure.shift(depth: depth, inc)
            self = .reflexive(of: value, as: erasure)
        case var .symmetry(proof):
            proof.shift(depth: depth, inc)
            self = .symmetry(proof)
        case var .rewrite(name, type, proof, term):
            type.shift(depth: depth + 1, inc)
            proof.shift(depth: depth, inc)
            term.shift(depth: depth, inc)
            self = .rewrite(name: name, type: type, proof: proof, term: term)
        case var .cast(proof, value0, value1):
            proof.shift(depth: depth, inc)
            value0.shift(depth: depth, inc)
            value1.shift(depth: depth, inc)
            self = .cast(proof: proof, value0: value0, value1: value1)
        case var .reference(ref):
            if !ref.clos {
                ref.term.shift(depth: depth, inc)
                self = .reference(ref)
            }
        }
    }
}

/// A context of variables.
/// Used to keep track of the variables in scope.
/// Variables are stored in a stack, with the most recent variable at the top.
/// The context is used to resolve variable names to indices.
public struct Context {

    /// The variables in the context.
    var context: [Variable] // TODO: consider using Deque here from swift collections

    /// An empty context with no variables.
    public static let empty = Context(context: [])

    /// Adds a variable to the context.
    /// - Parameters:
    ///   - name: The name of the variable.
    ///   - term: The associated term of the variable.
    /// - Returns: The index of the variable in the context.
    public mutating func extend(name: String, term: Term? = nil) {
        // TODO: use Var and appropriate shifts

        let term = term.map {term in
            var term = term
            term.shift(depth: 0, 1)
            return term
        } ?? .variable(index: 0)
        shift(depth: 0, 1)

        context.insert(Variable(name: name, term: term), at: 0)
    }

    /// Shifts the terms in the context to make room for new variables.
    private mutating func shift(depth: Int, _ inc: Int) {
        context.modifyEach {variable in variable.shift(depth: depth, inc)}
    }

    /// Returns the name of the variable at the given index.
    /// - Parameter index: The index of the variable.
    /// - Returns: The name of the variable.
    public func name(at index: Int) -> String?{
        guard index < context.count else {
            return nil
        }

        return context[index].name
    }

    /// Returns the term of the variable at the given index, which during type checking and inference is its type.
    /// - Parameter index: The index of the variable.
    /// - Returns: The term of the variable.
    public func type(of index: Int) -> Term {
        context[index].term
    }
}

// Enable the context to be used as a part of the parser's state.
extension Context: UserInfoKey {
    public typealias Value = Context
    public static var defaultValue: Value = Context(context: [])
}

extension Context {

    /// Indexes the context by name while skipping a number of variables with the same name.
    /// - Parameters:
    ///   - name: The name of the variable.
    ///   - skip: The number of variables with the same name to skip.
    /// - Returns: The variable with the given name, skipping the specified number of variables.
    subscript(name: Substring, skipping skip: Int) -> Variable? {
        precondition(skip >= 0)

        return context.lazy.filter {variable in variable.name == name }.prefix(skip + 1).last
    }

    /// Returns the index of the variable with the given name, skipping the specified number of variables.
    /// - Parameters:
    ///   - name: The name of the variable.
    ///   - skip: The number of variables with the same name to skip.
    /// - Returns: The index of the variable with the given name, skipping the specified number of variables.
    func index(of name: Substring, skipping skip: Int) -> Int? {
        precondition(skip >= 0)
        return context.lazy.enumerated().filter {variable in variable.1.name == name}.prefix(skip + 1).last.map {index, _ in index}
    }
}

extension Context: Equatable {

    /// Returns a Boolean value indicating whether two contexts are equal.
    public static func ==(lhs: Context, rhs: Context) -> Bool {
        lhs.context == rhs.context
    }
}
extension Context: Hashable {

    /// Hashes the context by feeding it into the given hasher.
    public func hash(into hasher: inout Hasher) {
        hasher.combine(context)
    }
}
