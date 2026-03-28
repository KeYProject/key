/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.wd;

import java.net.URL;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.RuleCollection;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.util.KeYResourceManager;

import org.key_project.logic.Choice;
import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (7/27/25)
 */
public class WdProfile extends JavaProfile {
    private static final Logger LOGGER = LoggerFactory.getLogger(WdProfile.class);

    public static final String PROFILE_ID = "java-wd";
    public static final String DISPLAY_NAME = "Java Profile + Well-Definedness Checks";

    public static final WdProfile INSTANCE = new WdProfile();


    private final RuleCollection wdStandardRules;

    public WdProfile() {
        super();

        var defRules = super.getStandardRules();

        final URL wdDotKey =
            KeYResourceManager.getManager().getResourceFile(Proof.class, "rules/wd.key");

        RuleSource tacletBaseWd = RuleSourceFactory.initRuleFile(
            Objects.requireNonNull(wdDotKey,
                "Could not find rule file 'rules/wd.key' in classpath"));

        wdStandardRules = new RuleCollection(defRules.getTacletBase()
                .append(tacletBaseWd),
            defRules.standardBuiltInRules());
    }

    @Override
    public String ident() {
        return PROFILE_ID;
    }

    @Override
    public String displayName() {
        return DISPLAY_NAME;
    }

    @Override
    public String description() {
        return "A profile for the verification of Java programs with incl. " +
            "well-definedness checks for JML specification. **Stability unknown**";
    }

    @Override
    public SpecificationRepository createSpecificationRepository(Services services) {
        return new SpecificationRepositoryWD(services);
    }

    @Override
    protected ImmutableList<BuiltInRule> initBuiltInRules() {
        var javaRules = super.initBuiltInRules();
        var rules = javaRules.map(it -> {
            if (it instanceof BlockContractInternalRule) {
                return WdBlockContractInternalRule.INSTANCE;
            } else if (it instanceof WhileInvariantRule) {
                return WdWhileInvariantRule.INSTANCE;
            } else
                return it;
        })
                .filter(it -> it != BlockContractExternalRule.INSTANCE)
                .filter(it -> !(it instanceof LoopContractExternalRule))
                .filter(it -> !(it instanceof LoopScopeInvariantRule));
        return rules;
    }

    @Override
    public boolean withPermissions() {
        return false;
    }

    @Override
    public RuleCollection getStandardRules() {
        return wdStandardRules;
    }

    /// {@inheritDoc}
    ///
    /// @param additionalProfileOptions a string representing the choice of `wdOperator`
    /// @return
    @Override
    public List<String> prepareInitConfig(InitConfig baseConfig,
            @Nullable Configuration additionalProfileOptions) {
        var warnings = new ArrayList<String>(2);
        var wdChoiceOn = baseConfig.choiceNS().lookup(new Name("wdChecks:on"));
        var wdChoiceOff = baseConfig.choiceNS().lookup(new Name("wdChecks:off"));

        if (baseConfig.isChoiceActive(wdChoiceOff)) {
            final var message =
                "wdChecks:off was set by in the init config, probably given in KeY file. This setting will be ignored";
            warnings.add(message);
            LOGGER.warn(message); // this logging is for finding the spot.
        }
        baseConfig.activateChoice(wdChoiceOn);


        if (additionalProfileOptions != null) {
            final var wdOperator = "wdOperator";
            final var selectedWdOperator = additionalProfileOptions.getString(wdOperator);
            if (selectedWdOperator == null) {
                return warnings;
            }

            var wdOperatorChoice = baseConfig.choiceNS().lookup(selectedWdOperator);
            if (wdOperatorChoice == null) {
                var choices = baseConfig.choiceNS().allElements()
                        .stream()
                        .filter(it -> wdOperator.equals(it.category()))
                        .map(Choice::toString)
                        .collect(Collectors.joining(", "));

                throw new IllegalStateException("Could not find choice for %s.\n  Choices known %s."
                        .formatted(additionalProfileOptions, choices));
            } else {
                if (baseConfig.isChoiceCategorySet(wdOperator)
                        && !baseConfig.isChoiceActive(wdOperatorChoice)) {
                    final var message = "Choice for wdOperator will be overwritten " +
                        "by profile as defined by user in the additional profile options.";
                    warnings.add(message);
                    LOGGER.warn(message); // this logging is for finding the spot.
                }
                baseConfig.activateChoice(wdOperatorChoice);
            }
        }
        return warnings;
    }
}
