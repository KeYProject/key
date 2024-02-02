/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init.loader;

import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.settings.Configuration;
import org.jspecify.annotations.NullMarked;

/**
 * Interface for writing the handling of the creation of proof obligations.
 * <p>
 * A proof obligation load takes the environment loaded from a key file, and instantiates this into the
 * initial sequent (called proof obligation). {@link ProofObligationLoader} are loaded with the help of the
 * {@link java.util.ServiceLoader}, hence you need to register them into the {@code META-INF} folder.
 * <p>
 * A {@link ProofObligationLoader} decides by itself whether it can handle a certain
 * {@link de.uka.ilkd.key.proof.init.KeYUserProblemFile},
 * by given the {@code class} entry from the file's {@code \proofObligation} configuration object.
 *
 * @author Alexander Weigl
 * @version 1 (28.12.23)
 */
@NullMarked
public interface ProofObligationLoader {

    /**
     * Builds the PO from the given environment and {@code \proofObligation} configuration.
     *
     * @param initConfig the key environment
     * @param properties the {@code \proofObligation} configuration
     * @return always a valid PO
     * @throws Exception in case of an arbitrary exception, e.g., missing information {@code properties}
     */
    IPersistablePO.LoadedPOContainer loadFrom(InitConfig initConfig, Configuration properties) throws Exception;

    /**
     * Receiving an identifier (tradiitonally the fully qualified class name) this method decides
     * whether it can handle the current situation. Curerntly the identifier corresponds to the {@code class} entry
     * in the {@code \proofObligation} entry in the {@link de.uka.ilkd.key.proof.init.KeYUserProblemFile}.
     *
     * @param identifier non-null string
     * @return true if this load handles this type of PO
     */
    boolean handles(String identifier);
}
