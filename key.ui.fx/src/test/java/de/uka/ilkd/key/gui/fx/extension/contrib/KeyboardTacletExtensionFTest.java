/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.gui.fx.docking.DockTitleActionF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleExecutor;
import org.key_project.prover.sequent.PosInOccurrence;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatCode;

/**
 * Toolkit-free tests of the FX port of the keyboard-taclet extension
 * ({@link KeyboardTacletExtensionF}), modelled after
 * {@code keyext.caching.fx/.../CachingExtensionFTest}: the service-loaded provider declares its
 * {@link KeYGuiExtensionF.Info} (mirroring the Swing
 * {@code de.uka.ilkd.key.gui.KeyboardTacletExtension} annotation, KeyboardTacletExtension.java:
 * 57-59), implements the portable SPI capabilities ({@code LeftPanelF} + {@code StartupF}) and is
 * headless-safe without an FX toolkit.
 * <p>
 * KNOWN-SIMPLIFIED: JavaFX 25 requires a running FX toolkit to even <em>construct</em> a control,
 * so the {@link KeyboardTacletPanelF} (like every FX control) is only verified by Gate 2's
 * in-app extension verification; the unit tests cover the toolkit-free surface: the provider,
 * the pure {@link KeyboardTacletModelF} (parity with the Swing {@code KeyboardTacletTest}) and
 * the check-style {@link DockTitleActionF} record.
 */
class KeyboardTacletExtensionFTest {

    private final KeyboardTacletExtensionF extension = new KeyboardTacletExtensionF();

    // ------------------------------------------------------------------
    // provider surface
    // ------------------------------------------------------------------

    @Test
    void infoAnnotationMirrorsSwingExtension() {
        KeYGuiExtensionF.Info info =
            KeyboardTacletExtensionF.class.getAnnotation(KeYGuiExtensionF.Info.class);
        assertThat(info).isNotNull();
        assertThat(info.name()).isEqualTo("Keyboard Taclet Control");
        assertThat(info.description())
                .isEqualTo(
                    "This extension control over the application of taclets via the keyboard.");
        assertThat(info.optional()).isTrue();
        // the Swing annotation omits experimental, so the Swing default applies
        // (KeYGuiExtension.java:88, mirrored by the FX annotation default)
        assertThat(info.experimental()).isTrue();
    }

    @Test
    void providerImplementsPortableCapabilities() {
        // the provider itself is constructible headless (no FX toolkit required); the Swing
        // original implements KeYGuiExtension + KeYGuiExtension.LeftPanel only
        // (KeyboardTacletExtension.java:60)
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.LeftPanelF.class);
        assertThat(extension).isInstanceOf(KeYGuiExtensionF.StartupF.class);
    }

    @Test
    void initIsHeadlessSafeWithoutMediator() {
        // the startup hook without a mediator (headless runs) must not crash and must not build
        // the panel (the lazy singleton only constructs controls once a window exists)
        assertThatCode(() -> extension.init(null, null)).doesNotThrowAnyException();
    }

    @Test
    void serviceRegistrationNamesTheProvider() throws IOException {
        try (InputStream in = KeyboardTacletExtensionFTest.class.getClassLoader()
                .getResourceAsStream(
                    "META-INF/services/de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF")) {
            assertThat(in).as("service-loader file on the classpath").isNotNull();
            String content = new String(in.readAllBytes(), StandardCharsets.UTF_8);
            assertThat(content)
                    .contains("de.uka.ilkd.key.gui.fx.extension.contrib.KeyboardTacletExtensionF");
        }
    }

    // ------------------------------------------------------------------
    // model parity with the Swing KeyboardTacletTest
    // ------------------------------------------------------------------

    @Test
    void prefixTableParityWithSwingKeyboardTacletTest() {
        // the exact expectations of the Swing key.ui KeyboardTacletTest.prefixTest
        assertThat(KeyboardTacletModelF.getPrefixLength("andLeft", "andRight")).isEqualTo(3);
        assertThat(KeyboardTacletModelF.getPrefixLength("cut", "cut_direct")).isEqualTo(3);
        assertThat(KeyboardTacletModelF.getPrefixLength("andLeft", "impRight")).isEqualTo(0);

        List<String> keywords =
            Arrays.asList("cut", "cut_direct", "andLeft", "andRight", "impRight");
        assertThat(KeyboardTacletModelF.getClashFreePrefix("impLeft", keywords)).isEqualTo(3);

        Map<String, String> table = KeyboardTacletModelF.buildPrefixTable(keywords);
        List<String> prefixes = table.keySet().stream().sorted().toList();
        assertThat(prefixes).containsExactly("andL", "andR", "cut", "cut_", "i");
    }

    @Test
    void modelGroupsApplicationsByRuleName() {
        KeyboardTacletModelF model = new KeyboardTacletModelF(
            List.of(new FakeRuleApp("impRight"), new FakeRuleApp("cut")));
        // Swing getTacletNames: the prefix table values, sorted
        // (KeyboardTacletExtension.java:527-529)
        assertThat(model.getTacletNames()).containsExactly("cut", "impRight");
        assertThat(model.getTaclets().get("cut")).hasSize(1);
    }

    @Test
    void processCharFollowsTheSwingSemantics() {
        KeyboardTacletModelF model = new KeyboardTacletModelF(List.of(new FakeRuleApp("cut")));
        // charValid is always true (KeyboardTacletExtension.java:440-442), so every typed
        // character extends the prefix
        model.processChar('$');
        assertThat(model.getCurrentPrefix()).isEqualTo("$");
        model.processChar('\u001B'); // escape resets prefix and position
        assertThat(model.getCurrentPrefix()).isEmpty();
        assertThat(model.getCurrentPos()).isEqualTo(-1);
        // backspace shortens the prefix, from a one-character prefix it clears it
        model.processChar('c');
        model.processChar('u');
        model.processChar('t');
        assertThat(model.getCurrentPrefix()).isEqualTo("cut");
        model.processChar('\b');
        assertThat(model.getCurrentPrefix()).isEqualTo("cu");
        model.processChar('\u001B');
        model.processChar('\b');
        assertThat(model.getCurrentPrefix()).isEmpty();
        // digits set the selection position AND are appended to the prefix
        // (KeyboardTacletExtension.java:467-475)
        model.processChar('0');
        assertThat(model.getCurrentPos()).isEqualTo(0);
        assertThat(model.getCurrentPrefix()).isEqualTo("0");
    }

    @Test
    void modelFiresPrefixPropertyChanges() {
        // the panel observes the model via PropertyChangeSupport (Swing wiring,
        // KeyboardTacletExtension.java:103-106/153-160)
        List<String> fired = new java.util.ArrayList<>();
        KeyboardTacletModelF model = new KeyboardTacletModelF(List.of(new FakeRuleApp("cut")));
        model.addPropertyChangeListener(KeyboardTacletModelF.PROP_CURRENT_PREFIX,
            e -> fired.add((String) e.getNewValue()));
        model.processChar('c');
        model.processChar('u');
        assertThat(fired).containsExactly("c", "cu");
    }

    @Test
    void selectedTacletsAppPrefersTheUniqueMatch() {
        // unique rule name: the single application is selected as soon as the prefix matches
        // (KeyboardTacletExtension.java:493-500, the t != null && t.size() == 1 branch)
        RuleApp cut = new FakeRuleApp("cut");
        RuleApp imp = new FakeRuleApp("impRight");
        KeyboardTacletModelF model = new KeyboardTacletModelF(List.of(cut, imp));
        model.processChar('c');
        assertThat(model.getSelectedTacletsApp()).contains(cut);
        // no prefix match (empty prefix selects nothing: currentPos is -1 and the
        // "cut_" clash key does not exist in the table)
        model.processChar('\u001B');
        assertThat(model.getSelectedTacletsApp()).isEmpty();
    }

    @Test
    void firstMatchingTacletAppWalksThePrefixTable() {
        // Swing getFirstMatchingTacletApp (KeyboardTacletExtension.java:502-511): the first
        // table key starting with the current prefix selects the first application of that rule
        RuleApp cut = new FakeRuleApp("cut");
        RuleApp imp = new FakeRuleApp("impRight");
        KeyboardTacletModelF model = new KeyboardTacletModelF(List.of(cut, imp));
        model.processChar('c');
        assertThat(model.getFirstMatchingTacletApp()).contains(cut);
        model.processChar('\u001B');
        model.processChar('i');
        assertThat(model.getFirstMatchingTacletApp()).contains(imp);
    }

    // ------------------------------------------------------------------
    // check-style title action record
    // ------------------------------------------------------------------

    @Test
    void dockTitleActionCheckStyleRecord() {
        Runnable noop = () -> {
        };
        // plain actions carry a null selected state
        assertThat(new DockTitleActionF("T", noop).selected()).isNull();
        assertThat(new DockTitleActionF("T", "tip", noop).selected()).isNull();
        // the check-style flavour (Swing DockingHelper.createCheckBox,
        // DockingHelper.java:188-223)
        assertThat(new DockTitleActionF("T", true, noop).selected()).isTrue();
        assertThat(new DockTitleActionF("T", false, noop).selected()).isFalse();
        assertThat(new DockTitleActionF("T", "tip", Boolean.TRUE, noop).selected()).isTrue();
    }

    // ------------------------------------------------------------------
    // fake rule application
    // ------------------------------------------------------------------

    /**
     * Minimal {@link RuleApp} fake for the toolkit-free model tests: only the rule name drives
     * the prefix-table logic under test, everything else is inert.
     */
    private record FakeRuleApp(String ruleName) implements RuleApp {
        @Override
        public Rule rule() {
            return new Rule() {
                @Override
                public Name name() {
                    return new Name(FakeRuleApp.this.ruleName);
                }

                @Override
                public <G extends ProofGoal<G>> RuleExecutor<G> getExecutor() {
                    throw new UnsupportedOperationException();
                }
            };
        }

        @Override
        public void checkApplicability() {
        }

        @Override
        public void registerSkolemConstants(Namespace<Function> fns) {
        }

        @Override
        public boolean complete() {
            return true;
        }

        @Override
        public PosInOccurrence posInOccurrence() {
            return null;
        }
    }
}
