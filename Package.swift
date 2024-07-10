// swift-tools-version: 5.10
// The swift-tools-version declares the minimum version of Swift required to build this package.

import PackageDescription

let package = Package(
    name: "cedille-core",
    platforms: [.macOS(.v13)],
    dependencies: [.package(url: "https://github.com/nearfri/Strix.git", from: "2.0.0")],
    targets: [
        // Targets are the basic building blocks of a package, defining a module or a test suite.
        // Targets can depend on other targets in this package and products from dependencies.
        .executableTarget(
            name: "CedilleCore", dependencies: [.product(name: "Strix", package: "Strix")]),
        .testTarget(name: "CedilleCoreTests", dependencies: ["CedilleCore"])
    ]
)
