## Contributing to ArkLib

We enthusiastically welcome contributions to ArkLib!

Whether you are fixing bugs, improving documentation, or adding new formalizations, your input is valuable. We particularly encourage contributions that address:

* **Active formalizations:** Please see the list of active formalization efforts and their blueprints.
* **Open Issues:** Please see the list of open issues for bugs, requested features, and specific formalization tasks. Issues tagged as `good first issue` or `help wanted` are great places to start.
* **Roadmap Goals:** We maintain a [ROADMAP](ROADMAP.md) outlining the planned direction and major goals for the library.
* **Documentation:** Documentation is actively being worked and will be available as soon as possible.

If you are interested in contributing but unsure where to begin, please get in touch.

### Large Contributions

For substantial contributions, such as a new proof system, we strongly encourage the development of a [blueprint](https://github.com/PatrickMassot/leanblueprint) first.

* **What is a Blueprint?** A blueprint is a document that outlines:
    * The contents of the formalization.
    * The proposed formalization strategy in Lean (key definitions, theorems, assumptions).
    * A dependency graph relating all intermediate results to the final desired result.
    * References to relevant literature.
    * Potential challenges and design choices.
* **Why a Blueprint?** This helps align the contribution with the project's structure and goals *before* significant coding and proving effort is invested. It facilitates discussion and feedback from maintainers and the community. It also makes it easier to manage large efforts in a distributed way.
* **Process:** Please open a new discussion or issue to propose your planned contribution and discuss the blueprint before starting implementation.

### Style Guide

ArkLib aims to align closely with the established conventions of the Lean community, particularly those used in `mathlib`.
Please follow the [mathlib Style Guide](https://github.com/leanprover-community/mathlib4/blob/master/CONTRIBUTING.md#style-guide-and-conventions).
This covers naming conventions, proof style, formatting, and more.

Adhering to this style guide ensures consistency across the library, making it easier for everyone to read, understand, and maintain the code. Our [linting script](`./scripts/lint-style.sh`) helps enforce some aspects of the style guide. Please ensure your code passes the linter checks.

## Code of Conduct

To ensure a welcoming and collaborative environment, ArkLib follows the principles outlined in the [mathlib Code of Conduct](https://github.com/leanprover-community/mathlib4/blob/master/CODE_OF_CONDUCT.md).

By participating in this project (e.g., contributing code, opening issues, commenting in discussions), you agree to abide by its terms. Please treat fellow contributors with respect. Unacceptable behavior can be reported to the project maintainers.

## Licensing

Like many other Lean projects, ArkLib is licensed under the terms of the Apache License 2.0 license. The full license text can be found in the [LICENSE](LICENSE) file.

By contributing to ArkLib, you agree that your contributions will be licensed under this same license. Ensure you are comfortable with these terms before submitting contributions.
