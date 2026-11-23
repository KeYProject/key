/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks that the boxed wrapper models in the JavaRedux classpath expose a
 * spec-public value field, a usable valueOf factory and a nullable TYPE field.
 * These are the primitives the autoboxing transformation desugars to.
 */
class AutoboxingWrapperModelTest {

    @BeforeAll
    static void enableJml() {
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                .setActiveStrategyProperties(new StrategyProperties());
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setUseJML(true);
    }

    private static void prove(String className, String source, Path dir) throws Exception {
        Path sub = Files.createDirectories(dir.resolve(className));
        Path file = sub.resolve(className + ".java");
        Files.writeString(file, source);

        KeYEnvironment<?> env = KeYEnvironment.load(file);
        try {
            var contract = env.getProofContracts().getFirst();
            Proof proof = env.createProof(contract.createProofObl(env.getInitConfig()));
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();
            assertTrue(proof.closed(),
                () -> "Proof did not close. Open goals: " + proof.openGoals());
        } finally {
            env.dispose();
        }
    }

    private static String model(String className, String body) {
        return """
                public class %s {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static strictfp void m() {
                        %s
                    }
                }
                """.formatted(className, body);
    }

    @Test
    void integerValueOfAndValueField(@TempDir Path dir) throws Exception {
        prove("IntegerModel", model("IntegerModel", """
                Integer a = Integer.valueOf(42);
                int i = a.value;
                //@ assert i == 42;
                """), dir);
    }

    @Test
    void longValueOfAndValueField(@TempDir Path dir) throws Exception {
        prove("LongModel", model("LongModel", """
                Long a = Long.valueOf(42L);
                long i = a.value;
                //@ assert i == 42L;
                """), dir);
    }

    @Test
    void byteValueOfAndValueField(@TempDir Path dir) throws Exception {
        prove("ByteModel", model("ByteModel", """
                Byte a = Byte.valueOf((byte) 42);
                byte i = a.value;
                //@ assert i == 42;
                """), dir);
    }

    @Test
    void shortValueOfAndValueField(@TempDir Path dir) throws Exception {
        prove("ShortModel", model("ShortModel", """
                Short a = Short.valueOf((short) 42);
                short i = a.value;
                //@ assert i == 42;
                """), dir);
    }

    @Test
    void characterValueOfAndValueField(@TempDir Path dir) throws Exception {
        prove("CharacterModel", model("CharacterModel", """
                Character a = Character.valueOf('x');
                char i = a.value;
                //@ assert i == 'x';
                """), dir);
    }

    @Test
    void booleanValueOfAndValueField(@TempDir Path dir) throws Exception {
        prove("BooleanModel", model("BooleanModel", """
                Boolean a = Boolean.valueOf(true);
                boolean i = a.value;
                //@ assert i;
                """), dir);
    }

    @Test
    void floatValueOfAndValueField(@TempDir Path dir) throws Exception {
        prove("FloatModel", model("FloatModel", """
                Float a = Float.valueOf(1.5f);
                float i = a.value;
                //@ assert a != null;
                """), dir);
    }

    @Test
    void doubleValueOfAndValueField(@TempDir Path dir) throws Exception {
        prove("DoubleModel", model("DoubleModel", """
                Double a = Double.valueOf(1.5d);
                double i = a.value;
                //@ assert a != null;
                """), dir);
    }

    @Test
    void floatNaNIsBoxable(@TempDir Path dir) throws Exception {
        prove("FloatNaNModel", model("FloatNaNModel", """
                Float a = Float.valueOf(0.0f / 0.0f);
                float i = a.value;
                //@ assert a != null;
                """), dir);
    }

    @Test
    void staticTypeFieldIsNullable(@TempDir Path dir) throws Exception {
        prove("TypeModel", model("TypeModel", """
                Integer a = Integer.valueOf(42);
                //@ assert a != null;
                """), dir);
    }
}
