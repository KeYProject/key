# Agent Guidelines for KeY Project

This document provides guidelines and rules for AI agents working on the KeY deductive Java program verifier project.

## Project Overview

**KeY** is an interactive theorem prover for formal verification and analysis of Java programs. It supports:
- Formal verification of Java programs with Java Modeling Language specifications
- Symbolic program execution
- First-order reasoning
- Test case generation

**License**: GPL v2 (all contributions must be compatible)

## Technical Stack

### Build System
- **Gradle** with Groovy DSL (`build.gradle`)
- Multi-module project structure
- Java 21 compatibility required

```bash
# Common build commands
./gradlew classes                   # Compile all classes
./gradlew testClasses               # Compile all test classes
./gradlew test                      # Run full test suite (hours)
./gradlew testFast                  # Run lightweight tests (minutes)
./gradlew spotlessApply             # Reformat source code
./gradlew :key.<subproject>:test --tests "<class>.<method>"  # Specific test
./gradlew :key.ui:run               # Run KeY UI
./gradlew :key.ui:run --args='--experimental'  # With experimental features
./gradlew :key.ui:shadowJar         # Create fat jar
```

### Key Technologies
- **Java 21** (source/target compatibility)
- **JUnit 6** (Jupiter) for testing
- **AssertJ** for assertions
- **SLF4J** with Logback for logging
- **Spotless** for code formatting
- **ANTLR 4** for parser generation

### Dependencies Management
- Version Catalog (`libs.*` notation in build files)
- All dependencies must be on Maven Central repository
- Use JSpecify for nullability annotations

## Project Structure

### Core Modules
```
key.util          - Base utilities
key.core          - Core verification engine
key.ui            - GUI application
key.ncore         - Logic layer
key.ncore.*       - Calculus layers
```
Extension Modules are marked by name `keyext.*`

### Module Naming Convention
- Base components: `key.*`
- Extensions/plugins: `keyext.*`
- Follow Maven standard directory layout

## Coding Conventions

### Java Code Style
- Follow [Java Code Conventions](https://keyproject.github.io/key-docs/devel/CodingConventions/)
- Use Spotless plugin for automatic formatting
- Indentation: 4 spaces (no tabs)
- Line length: Reasonable limits (typically 120 chars)
- Braces: Always use braces for control structures

### Package Structure
- Root packages: `de.uka.ilkd.key.*`, `org.key_project.*`
- Keep related classes in same package
- Avoid circular dependencies between modules

### Documentation
- JavaDoc for public APIs
- Inline comments for complex logic
- Reference official docs: https://keyproject.github.io/key-docs/devel/

## Testing Guidelines

### Test Organization
- Tests in `src/test/java` mirroring source structure
- Test fixtures in `src/testFixtures/java`
- Use JUnit 5 Jupiter API
- Prefer AssertJ for fluent assertions

### Writing Tests
```java
// Example pattern
@Test
void shouldVerifyExpectedBehavior() {
    // Given
    // When  
    // Then - use AssertJ
    assertThat(result).isEqualTo(expected);
}
```

### Running Tests
- Use `testFast` for quick feedback during development
- Use `test` before committing (comprehensive but slow)
- Debug with: `./gradlew test --debug-jvm` (attach at localhost:5005)

## Quality Assurance

### Automated Checks
All PRs are automatically checked via GitHub Actions:
- Unit tests execution
- Code formatting (Spotless)
- Static analysis (Checker Framework, SonarQube)
- License compliance

### Pre-commit Checklist
1. Code compiles: `./gradlew classes`
2. Tests pass: `./gradlew testFast`
3. Reformatting: `./gradlew spotlessApply`
4. No new warnings introduced
5. GPL v2 license compatibility verified

## Development Workflow

### Branch Strategy
- Feature branches from main
- Descriptive branch names (e.g., `lastname/xxx`, `feature/xxx`, `fix/yyy`)
- Releases are in `releases/` and pre-releases in `prerelease/`
- Rebase before merging to keep history clean

### Commit Messages
- Clear, descriptive messages
- Reference issues when applicable
- Follow conventional commits pattern

### Pull Requests
1. Fork and create feature branch
2. Implement changes with tests
3. Ensure all CI checks pass
4. Open PR with clear description
5. Address review feedback
6. Squash/rebase as requested

## Architecture Principles

### Core Design
- Separation of concerns between layers
- Immutable data structures where possible
- Thread-safety considerations documented
- Performance-critical code profiled

### Key Components
- **Proof Engine**: Sequent calculus-based theorem proving
- **SMT Integration**: Z3, cvc5, Princess solvers
- **GUI**: Java Swing with FlatLaf look-and-feel

## Tools & Resources

### Essential Links
- Homepage: https://key-project.org
- Developer Docs: https://keyproject.github.io/key-docs/devel/
- Issue Tracker: https://github.com/KeYProject/key/issues
- Mailing List: key-all@lists.informatik.kit.edu

### IDE Setup
- IntelliJ IDEA recommended (project includes `.idea` configs)
- Eclipse supported via gradle eclipse plugin
- Enable annotation processing for Checker Framework

## Agent-Specific Rules

### When Making Changes
1. **Understand context first**: Read existing code, tests, and documentation
2. **Follow patterns**: Match existing code style and architecture
3. **Test incrementally**: Verify each change compiles and tests pass
4. **Document decisions**: Add comments explaining non-obvious choices
5. **Respect licensing**: All code must be GPL v2 compatible

### Communication
- Be explicit about assumptions and limitations
- Provide complete, functional code (no placeholders)
- Include usage examples when adding new features
- Reference relevant documentation or prior art

### Code Review Expectations
- Manual review by core team required
- Automated checks must pass first
- Be prepared to iterate based on feedback
- Maintain backward compatibility when possible

## Common Tasks Reference

### Adding a New Module
1. Create directory following pattern: `key.module.name/`
2. Add to `settings.gradle`
3. Configure `build.gradle` with dependencies
4. Apply standard plugins (java, spotless, checkerframework)

### Modifying Build Configuration
1. Edit root `build.gradle` for global changes
2. Edit subproject `build.gradle` for module-specific changes
3. Update version catalog if adding dependencies
4. Test build locally before committing

### Debugging Issues
1. Check existing issues/PRs for similar problems
2. Enable debug logging
3. Use debugger attachment (localhost:5005)
4. Consult developer documentation
5. Ask on mailing list if stuck

---

*Last updated: August 2026*
*For questions, refer to the [KeY Developer Documentation](https://keyproject.github.io/key-docs/devel/)*
