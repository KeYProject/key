# Soundiness Info Window - Design Document

## Overview

This document describes the design and implementation for a **Soundiness Info Window** in KeY, as implemented on July 3, 2026.

---

## What is Soundiness?

**Soundiness** refers to the practical trade-offs made in formal verification tools between complete soundness and usability. Unlike binary soundness (sound/unsound), soundiness acknowledges a spectrum of assumptions and simplifications that affect verification validity.

See: [Soundiness - Communications of the ACM](https://yanniss.github.io/Soundiness-CACM.pdf)

In KeY's context, soundiness encompasses:
- Taclet options that disable certain checks for usability
- Platform limitations (memory, timeouts)
- Incomplete source code analysis
- Proof techniques that rely on unproved lemmas or assumptions

---

## User Requirements

### Goal
Provide non-expert KeY users with a **comprehensive, understandable report** explaining what assumptions and limitations affect their verification results.

### Key Design Decisions

| Question | Decision | Rationale |
|----------|----------|-----------|
| **Q1: Aggregate risk score?** | ❌ No aggregate level | Users should see individual warnings without oversimplification |
| **Q2: Detail level?** | ✅ Full detail in HTML format | Simple, readable format that works in Swing |
| **Q3: Proof tree analysis depth?** | ✅ Full traversal | Users need to find where assumptions are used |
| **Q4: Batch analysis?** | ❌ Not for v1 | Focus on single-proof experience first |
| **Q5: Report persistence?** | ❌ Compute fresh each time | Settings may change; always show current state |
| **Q6: Memory warning thresholds?** | ✅ Yes (<1GB critical, <2GB warning) | Concrete thresholds help users understand limits |

---

## Four Compartments

The soundiness report is organized into four distinct compartments:

### Compartment 1: General KeY Settings
*"Platform and tool limitations that affect verification"*

**Data Sources:**
- `Runtime.getRuntime().maxMemory()` - JVM memory limits
- `ChoiceSettings.getChoice("initialisation")` - Static initialization setting
- `StrategySettings.getMaxSteps()` - Proof search limits
- `GeneralSettings.isUseJML()` - JML enabled/disabled
- `GeneralSettings.isEnsureSourceConsistency()` - Source caching

**Warning Examples:**
| Category | Condition | User Message |
|----------|-----------|--------------|
| Memory | < 1GB available | "Very limited memory available" |
| Memory | < 2GB available | "Limited memory available" |
| Static Initialization | `disableStaticInitialisation` | "Static constructors are not analyzed" |
| JML Disabled | `isUseJML() == false` | "JML specifications are ignored" |
| Source Caching | `isEnsureSourceConsistency() == false` | "Source file changes may not be detected" |

---

### Compartment 2: Taclet Options
*"Semantic simplifications in the logical calculus"*

**Current KeY Classification:**

```java
// UNSOUND choices (TacletOptionsSettings.isUnsound())
- runtimeExceptions:ignore
- initialisation:disableStaticInitialisation  
- intRules:arithmeticSemanticsIgnoringOF

// INCOMPLETE choices (isIncomplete())
- runtimeExceptions:ban
- Strings:off
- intRules:arithmeticSemanticsCheckingOF
- integerSimplificationRules:minimal
- programRules:None

// CONDITIONAL (getInformation())
- JavaCard:on/off (sound only for respective platform)
- assertions:on/off (depends on JVM startup flags)
```

**Enhanced Presentation:**

| Choice | Plain English Impact | Severity |
|--------|---------------------|----------|
| `runtimeExceptions:ignore` | "Assumes no null pointer, divide-by-zero, or array bounds errors occur" | 🔴 High |
| `intRules:arithmeticSemanticsIgnoringOF` | "Integer overflow is ignored; arithmetic wraps around like in Java" | 🔴 High |
| `initialisation:disableStaticInitialisation` | "Static field initializers and static blocks are skipped" | 🔴 High |
| `Strings:off` | "String operations are not analyzed" | 🟡 Medium |
| `programRules:None` | "Java language constructs are not processed" | 🔴 High |
| `runtimeExceptions:ban` | "Any implicit runtime exception is treated as program failure" | 🟢 Low |

---

### Compartment 3: Source Analysis
*"What was actually loaded and parsed"*

**Information Displayed:**
- Count of loaded `.java` and `.key` files
- Parse warnings and errors
- Missing class dependencies
- JML contract coverage (% of methods with specifications)
- Unsupported Java features (lambdas, streams, etc.)

**Note:** Currently returns empty data; full implementation requires integration with KeYFile/InitConfig.

---

### Compartment 4: Proof Tree Analysis
*"What happened during this specific proof"*

**Analysis Components:**

1. **Goal Statistics**
   - Total goals, closed goals, open goals
   - Cached goals (from proof cache)

2. **User-Defined Lemmas**
   - Scan for taclets with "lemma" in name
   - Track usage count
   - Flag unproved lemmas

3. **Assumptions**
   - Count of `assume` commands used
   - Location and formula for each assumption

4. **Rule Application Statistics**
   - Most frequently used rules (top 5)
   - Interactive vs. automated steps ratio

---

## Technical Architecture

### Implementation Approach

The implementation uses a **single HTML generation approach** rather than separate data models and UI components:

**Location:** `/opencode/key.ui/src/main/java/de/uka/ilkd/key/gui/soundiness/SoundinessAnalyzer.java`

```java
public final class SoundinessAnalyzer {
    
    /**
     * Generates an HTML soundiness report for the given proof.
     * 
     * @param proof the proof to analyze
     * @return HTML string containing the complete report
     */
    public static String generateHTMLReport(Proof proof);
}
```

**Internal Data Records** (encapsulated within analyzer):
- `GeneralKeYWarning` - Warning with level, category, message, recommendation
- `TacletOptionEntry` - Taclet choice with impact description
- `SourceStats` - Source file statistics
- `ProofStats` - Proof tree statistics
- `LemmaUsage` - Lemma usage tracking
- `AssumptionUsage` - Assumption tracking

---

### Dialog UI

**Location:** `/opencode/key.ui/src/main/java/de/uka/ilkd/key/gui/soundiness/SoundinessDialog.java`

Simple modal `JDialog` with:
- HTML pane displaying the generated report
- Scroll pane with wheel scrolling enabled
- Copy HTML button
- Close button

**UI Layout:**
```
┌─────────────────────────────────────────────────────┐
│  Soundiness Report: [Proof Name]                    │
├─────────────────────────────────────────────────────┤
│                                                     │
│  [Scrollable HTML Report]                           │
│  - 1. General KeY Settings                          │
│  - 2. Taclet Options                                │
│  - 3. Source Analysis                               │
│  - 4. Proof Tree Analysis                           │
│                                                     │
│        [Copy HTML]  [Close]                         │
└─────────────────────────────────────────────────────┘
```

---

## Integration Points

### 1. TaskTree Icon Enhancement
**File:** `TaskTree.java:TaskTreeIconCellRenderer.getTreeCellRendererComponent()`

Add overlay icon when proof has unsound choices or assumptions:
- Icon: Use existing `IconFactory.WARNING_UNSOUND`
- Tooltip: Brief summary like "2 unsound choices, 1 assumption used"

### 2. Proof Statistics Dialog
**File:** `ShowProofStatistics.java:Window.init()`

Add button after line ~338:
```java
JButton soundinessButton = new JButton("Show Soundiness Report");
soundinessButton.setIcon(IconFactory.WARNING_UNSOUND.get());
soundinessButton.addActionListener(e -> {
    de.uka.ilkd.key.gui.soundiness.SoundinessDialog dialog = 
        new de.uka.ilkd.key.gui.soundiness.SoundinessDialog(mainWindow, proof);
    dialog.setVisible(true);
});
buttonPane2.add(soundinessButton);
```

### 3. Context Menu Extension
**File:** `ShowSoundinessAction.java`

Register via KeY extension mechanism to add "Show Soundiness Report" to proof list right-click menu.

### 4. Proof Finished Notification
**File:** `ProofClosedJTextPaneDisplay.java:execute()`

After showing statistics, optionally add link: "⚠ This proof used unsound options. [View Details]"

---

## Code Conventions

### Naming
- Use `Soundiness` prefix consistently (not `Soundness`)
- Private constructors for utility classes
- Internal records use descriptive names

### Documentation
- Javadoc for public APIs
- Include `@since 2.13` tag
- Link to this document in package-info.java

### Error Handling
- Never fail silently - log warnings to SLF4J
- Handle null proofs gracefully
- Catch exceptions during analysis and show partial results

---

## Testing Strategy

### Manual Testing Scenarios
1. Proof with all 3 unsound choices enabled
2. Proof using `\lemma` taclets without side proofs
3. Proof with multiple `assume` commands
4. Minimal proof (single goal, few steps)
5. Proof closed via cache
6. Large proof (>1000 nodes) - verify performance acceptable (<2s analysis)

---

## Performance Considerations

### Current Implementation
- Single-pass analysis for all compartments
- HTML generated on-demand
- No caching (report computed fresh each time)

### Future Optimization
For very large proofs, consider:
- Background thread analysis
- Lazy loading of compartments
- Caching with invalidation on proof structure changes

---

## Risks and Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Proof tree traversal too slow | Poor UX for large proofs | Profile and optimize if needed |
| Too many false positives | Users ignore warnings | Careful calibration, user feedback loop |
| Technical jargon in messages | Confuses non-experts | Iterate on wording based on feedback |
| Integration conflicts with extensions | Broken functionality | Test with popular extensions |

---

## Future Enhancements (Post-v1)

- [ ] Batch analysis ("Analyze All Loaded Proofs")
- [ ] Persistent soundiness metadata in proof bundles
- [ ] Aggregate statistics across proof corpus
- [ ] Automatic recommendations ("Consider enabling X for more complete verification")
- [ ] Integration with SMT solver trust levels
- [ ] Historical tracking (how soundiness changed during proof development)
- [ ] Enhanced source analysis with real KeYFile data
- [ ] Proper lemma detection via \lemma annotation parsing

---

## References

- [Soundiness - CACM Paper](https://yanniss.github.io/Soundiness-CACM.pdf)
- `TacletOptionsSettings.java` - existing taclet option handling
- `ShowProofStatistics.java` - similar dialog pattern
- `TaskTree.java` - proof list rendering

---

## Contact

For questions about this implementation, contact the KeY development team.

**Document Version:** 2.0  
**Created:** 2026-07-03  
**Updated:** 2026-07-03 (Simplified HTML generation approach)  
**Status:** ✅ Implemented
