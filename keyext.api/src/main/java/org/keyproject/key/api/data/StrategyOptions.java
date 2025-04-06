/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import java.lang.reflect.Field;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.StrategySettings;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record StrategyOptions(
        String method,
        String dep,
        String query,
        String nonLinArith,
        String stopMode,
        int maxSteps) implements KeYDataTransferObject {
    public static StrategyOptions defaultOptions() {
        return new StrategyOptions(
            "METHOD_CONTRACT",
            "DEP_ON",
            "QUERY_ON",
            "NON_LIN_ARITH_DEF_OPS",
            "STOPMODE_NONCLOSE",
            1000);
    }

    public static StrategyOptions from(StrategySettings settings) {
        var sp = settings.getActiveStrategyProperties();
        return new StrategyOptions(
            sp.getProperty(StrategyProperties.METHOD_OPTIONS_KEY),
            sp.getProperty(StrategyProperties.DEP_OPTIONS_KEY),
            sp.getProperty(StrategyProperties.QUERY_OPTIONS_KEY),
            sp.getProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY),
            sp.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY),
            settings.getMaxSteps());
    }

    private String getVal(String key) {
        Field f = null;
        try {
            f = StrategyProperties.class.getField(key);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException("Unknown key: " + key);
        }
        Class<?> t = f.getType();
        if (t == String.class) {
            try {
                return (String) f.get(this);
            } catch (IllegalAccessException e) {
                throw new RuntimeException("Cannot access field: " + key);
            }
        } else {
            throw new RuntimeException("Type mismatch: " + t);
        }
    }

    public void configure(Proof proof) {
        var defaultOptions = defaultOptions();
        StrategyProperties sp = proof.getSettings().getStrategySettings()
                .getActiveStrategyProperties();
        if (method != null) {
            sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, getVal(method));
        } else {
            sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, defaultOptions.method());
        }
        if (dep != null) {
            sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, getVal(dep));
        } else {
            sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, defaultOptions.dep());
        }
        if (query != null) {
            sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, getVal(query));
        } else {
            sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, defaultOptions.query());
        }
        if (nonLinArith != null) {
            sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, getVal(nonLinArith));
        } else {
            sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
                defaultOptions.nonLinArith());
        }
        if (stopMode != null) {
            sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, getVal(stopMode));
        } else {
            sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, defaultOptions.stopMode());
        }
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
        proof.getSettings().getStrategySettings().setMaxSteps(maxSteps);
    }
}
