## Description: Make Packages Sealable

### Overview
This pull request refactors the KeY project's package structure to enable Java package sealing—a security feature that prevents unauthorized classes from being added to critical packages. The changes involve extensive package reorganization and restructuring across 470 files.

### What are Sealable Packages and Why Are They Useful?

**Sealable packages** (also called sealed packages) are a Java security mechanism where you can seal a package within a JAR file to prevent other code from adding classes to that package. This is valuable because:

1. **Security Hardening**: Prevents attackers from injecting malicious classes into core packages by adding them to the classpath or loading them dynamically
2. **API Integrity**: Protects internal package structures—external code cannot define new classes in sealed packages, ensuring the API remains stable and predictable
3. **Modularity**: Clearly demarcates which packages are public/stable versus internal, reducing accidental coupling to implementation details
4. **Version Safety**: When deploying updates, sealed packages guarantee that no legacy or conflicting versions of package-internal classes will be loaded from other JARs

### Main Changes in This PR

The PR makes packages sealable by:

1. **Package Reorganization**: Moving files from overly broad packages into more specific, focused packages:
   - GUI-related classes moved to `de.uka.ilkd.key.ui.gui.*`
   - Core UI infrastructure moved to `de.uka.ilkd.key.ui.core.*`
   - Symbolic execution utilities organized under `de.uka.ilkd.key.symbolic_execution.*`
   - Other internal utilities properly scoped under `de.uka.ilkd.key.ui.*`

2. **Updated Imports**: Adjusts 470 import statements throughout the codebase to reflect the new package structure

3. **Build Configuration**: Adds JAR manifest configuration to set the `Sealed: true` attribute, enabling the sealing mechanism

### Type of pull request

- ✓ Refactoring (behaviour should not change or only minimally change)
- ✓ There are changes to the (Java) code
- ✓ There are changes to the deployment/CI infrastructure (gradle, github, ...)

### Status
This PR is currently in draft mode and targets the v3.0.0 milestone. The scope is substantial (1,675 additions, 1,499 deletions across 470 files).

### Ensuring quality

- Code reorganization maintains all existing functionality
- Import statements updated to reflect new package structure
- Build configuration updated to enable package sealing

The contributions within this pull request are licensed under GPLv2 (only) for inclusion in KeY.
