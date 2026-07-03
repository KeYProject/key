# Soundiness Info Window - Implementation Summary

## Status: ✅ Complete - HTML Report Generation

**Date:** July 3, 2026  
**Compilation:** SUCCESS (key.ui module)

---

## Files Created

### Core Implementation (in `key.ui/src/main/java/de/uka/ilkd/key/gui/soundiness/`)

1. **SoundinessAnalyzer.java**
   - Static utility class that generates HTML reports directly
   - Single public method: `generateHTMLReport(Proof proof)`
   - Internal data records (encapsulated):
     - `GeneralKeYWarning` - Warning with level, category, message, recommendation
     - `TacletOptionEntry` - Taclet choice with impact description
     - `SourceStats` - Source file statistics (skeleton)
     - `ProofStats` - Proof tree statistics
     - `LemmaUsage` - Lemma usage tracking
     - `AssumptionUsage` - Assumption tracking

2. **SoundinessDialog.java**
   - Simple modal JDialog (75 lines)
   - Displays HTML in scrollable JEditorPane
   - Wheel scrolling enabled
   - Copy HTML button
   - Close button

---

## Implementation Details

### Compartment 1: General KeY Settings ✅
- Memory threshold checks (<1GB critical, <2GB warning)
- Static initialization detection
- JML enabled/disabled check
- Source consistency caching status
- Strategy step limit warnings

### Compartment 2: Taclet Options ✅
- All active choices analyzed
- Plain English impact descriptions
- Affected features listed
- Unsound choices highlighted in red
- Incomplete choices in orange

### Compartment 3: Source Analysis ⚠️ (Skeleton)
- Returns empty data structure
- Ready for integration with KeYFile/InitConfig

### Compartment 4: Proof Tree Analysis ✅
- Full tree traversal via subtreeIterator()
- Goal counting (open/closed/cached)
- Lemma usage detection (by name pattern)
- Assume command detection
- Rule application statistics (top 5 most used)
- Interactive vs automated steps

---

## Integration Points (Completed)

### 1. Proof Statistics Dialog ✅
**File:** `ShowProofStatistics.java:Window.init()` (line ~320)

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

### 2. Context Menu Extension ✅
**File:** `ShowSoundinessAction.java`
- Registered via extension mechanism
- Adds "Show Soundiness Report" to proof list right-click menu

### 3. Extension Point ✅
**File:** `SoundinessExtension.java`
- Implements KeYGuiExtension and KeYGuiExtension.ContextMenu
- Provides context menu integration

---

## Integration Points (Not Yet Implemented)

1. **TaskTree Icon Enhancement**
   - File: TaskTree.java:TaskTreeIconCellRenderer
   - Add overlay icon when proof has warnings
   - Tooltip with summary

2. **Proof Finished Notification**
   - File: ProofClosedJTextPaneDisplay.java
   - Optional link to view soundiness details

---

## Technical Decisions

### Simplified Architecture
The original design called for separate data model records and UI components. The final implementation uses a **single HTML generation approach**:

**Advantages:**
- Simpler codebase (2 files vs 8 files)
- No Swing component complexity
- Easy to export/share reports
- Consistent rendering across platforms
- No timestamp formatting issues with Instant

**Trade-offs:**
- Less flexible for programmatic access to data
- HTML must be parsed if data needed elsewhere

### Package Structure
All classes in `de.uka.ilkd.key.gui.soundiness` package

### Data Encapsulation
Internal records are private to the analyzer, preventing external dependencies on implementation details.

---

## Known Issues / Limitations

1. **Source Analysis** - Returns empty data; needs integration with KeYFile/InitConfig
2. **Lemma Detection** - Simplified check based on name containing "lemma"; should check \lemma annotation properly
3. **Performance** - No background threading yet for very large proofs
4. **No Aggregate Metrics** - Deliberately avoided per design decision

---

## Build Information

**Module:** key.ui  
**Java Version:** 21.0.11  
**Gradle Command:** `./gradlew :key.ui:compileJava`  
**Result:** BUILD SUCCESSFUL

---

## Usage Example

```java
// Show dialog from existing code
new SoundinessDialog(mainWindow, proof).setVisible(true);

// Get raw HTML (for export or other purposes)
String html = SoundinessAnalyzer.generateHTMLReport(proof);
```

---

## References

- Design Document: AGENT.soundiness.md
- Soundiness Paper: https://yanniss.github.io/Soundiness-CACM.pdf
- Existing similar code: ShowProofStatistics.java, TacletOptionsSettings.java
