/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.settings.ProofSettings;

import org.jspecify.annotations.NonNull;


/**
 * A little helper class to resolve the settings for treatment of final fields.
 *
 * During the generation of {@link de.uka.ilkd.key.proof.init.ProofOblInput}s, we need to know
 * which final-treatment is activated. Also during translation from JML to JavaDL this is needed.
 * Unfortunately, the settings are not directly available everywhere, so there is a mechanism to
 * remember the setting while it is available in a thread-local variable. This class provides a
 * simple interface to access this boolean variable.
 *
 * The alternative would be to make the settings available at more spots ...
 *
 * @author Mattias Ulbrich
 */
public class FinalHeapResolution {

    private static final ThreadLocal<Boolean> finalEnabledVariable = new ThreadLocal<>();
    private static final String SETTING = "finalFields";
    private static final String IMMUTABLE_OPTION = SETTING + ":immutable";

    /**
     * Returns whether final fields are treated different from normal fields as immutable data.
     *
     * If initConfig does not have settings yet, the default settings are used.
     *
     * @param initConfig the configuration to read the settings from
     * @return true if final fields are treated as immutable
     */
    public static boolean isFinalEnabled(@NonNull InitConfig initConfig) {
        ProofSettings settings = initConfig.getSettings();
        if (settings == null) {
            settings = new ProofSettings(ProofSettings.DEFAULT_SETTINGS);
        }
        return isFinalEnabled(settings);
    }

    /**
     * Returns whether final fields are treated different from normal fields as immutable data.
     *
     * @param settings the settings to read the settings from
     * @return true if final fields are treated as immutable
     */
    public static boolean isFinalEnabled(@NonNull ProofSettings settings) {
        return settings.getChoiceSettings().getDefaultChoices().get(SETTING)
                .equals(IMMUTABLE_OPTION);
    }

    /**
     * Remembers if final fields are treated differently from normal fields as immutable flag
     * in a thread-local variable that can be recalled later using {@link #recallIsFinalEnabled()}.
     *
     * @param initConfig the configuration to read the settings from
     */
    public static void rememberIfFinalEnabled(InitConfig initConfig) {
        finalEnabledVariable.set(isFinalEnabled(initConfig));
    }

    /**
     * Recall a previously stored status regarding the treatment of final fields.
     * See {@link #rememberIfFinalEnabled(InitConfig)}.
     *
     * @return true if final fields are treated as immutable (as recorded earlier)
     * @throws IllegalStateException if the variable has not been set before
     */

    public static boolean recallIsFinalEnabled() {
        Boolean bool = finalEnabledVariable.get();
        if (bool == null) {
            throw new IllegalStateException("Unset final enabled variable");
        }
        return bool.booleanValue();
    }
}
