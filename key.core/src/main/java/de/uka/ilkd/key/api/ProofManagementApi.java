/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.api;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.KeYTypeUtil;

import org.key_project.util.collection.ImmutableSet;

/**
 * This class serves as a facade to all functionalities that are needed for proof management, i.e.,
 * loading proof files, retrieving the proof obligations
 *
 * @author Sarah Grebing.
 */
public class ProofManagementApi {
    private final KeYEnvironment<?> currentEnv;
    private final List<Contract> proofContracts = new ArrayList<>();
    private HashSet<String> ruleNames;

    public ProofManagementApi(KeYEnvironment<?> env) {
        currentEnv = env;
    }

    public Services getServices() {
        return currentEnv.getServices();
    }

    /**
     * Retrieve a list of all available contracts
     *
     * @return {@link List<Contract>}; can be null if no file was loaded before (we should throw an
     *         exception here)
     */
    public List<Contract> getProofContracts() {
        if (proofContracts.isEmpty()) {
            buildContracts();
        }
        return proofContracts;
    }

    /**
     * constructs the possible proof contracts from the java info in the environment.
     */
    private void buildContracts() {
        proofContracts.clear();
        Set<KeYJavaType> kjts = currentEnv.getJavaInfo().getAllKeYJavaTypes();
        for (KeYJavaType type : kjts) {
            if (!KeYTypeUtil.isLibraryClass(type)) {
                ImmutableSet<IObserverFunction> targets =
                    currentEnv.getSpecificationRepository().getContractTargets(type);
                for (IObserverFunction target : targets) {
                    ImmutableSet<Contract> contracts =
                        currentEnv.getSpecificationRepository().getContracts(type, target);
                    for (Contract contract : contracts) {
                        proofContracts.add(contract);
                    }
                }
            }
        }
    }

    /**
     * @param contract
     * @return
     * @throws ProofInputException
     */
    public ProofApi startProof(ProofOblInput contract) throws ProofInputException {
        return new ProofApi(currentEnv.createProof(contract), currentEnv);
    }

    /**
     * @param contract
     * @return
     * @throws ProofInputException
     */
    public ProofApi startProof(Contract contract) throws ProofInputException {
        return startProof(contract.createProofObl(currentEnv.getInitConfig(), contract));
    }

    public ProofApi getLoadedProof() {
        return new ProofApi(currentEnv.getLoadedProof(), currentEnv);
    }

    /**
     * Constructs a set containing all names of a taclets that are registered in the current
     * environment.
     * <p>
     * The result is cached to speed up further calls.s
     *
     * @return always returns a non-null hash set.
     */
    public Set<String> getRuleNames() {
        if (ruleNames == null) {
            ruleNames = new HashSet<>();
            currentEnv.getInitConfig().activatedTaclets()
                    .forEach(taclet -> ruleNames.add(taclet.displayName()));

            currentEnv.getInitConfig().builtInRules().forEach(t -> ruleNames.add(t.displayName()));
        }
        return ruleNames;
    }

    /*
     * public KeYApi.CommandType getCommandType(String identifier) { if
     * (KeYApi.getMacroApi().getMacro(identifier) != null) { return KeYApi.CommandType.MACRO; }
     *
     * if (KeYApi.getScriptCommandApi().getScriptCommands(identifier) != null) { return
     * KeYApi.CommandType.SCRIPT; }
     *
     * if (getRuleNames().contains(identifier)) { return KeYApi.CommandType.RULE; }
     *
     * return KeYApi.CommandType.UNKNOWN; }
     *
     * enum CommandType { SCRIPT, RULE, MACRO, UNKNOWN; }
     */
}
