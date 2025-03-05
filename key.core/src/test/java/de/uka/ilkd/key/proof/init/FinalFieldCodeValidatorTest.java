/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.io.File;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Stream;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.KeYTypeUtil;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

class FinalFieldCodeValidatorTest {

    @TestFactory
    public Stream<DynamicTest> testCodeValidatorParse() throws ProblemLoaderException {
        return testContracts(false, "final/shouldparse");
    }

    @TestFactory
    public Stream<DynamicTest> testCodeValidatorFail() throws ProblemLoaderException {
        return testContracts(true, "final/shouldfail");
    }

    private Stream<DynamicTest> testContracts(boolean shouldfail, String directory)
            throws ProblemLoaderException {
        URL url = getClass().getResource(directory);
        assert url != null : directory + " not found.";
        assert "file".equals(url.getProtocol()) : "Test cases must be in file system";
        File dir = new File(url.getPath());
        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(dir, null, null, null);

        Set<KeYJavaType> kjts = env.getJavaInfo().getAllKeYJavaTypes();
        Set<Contract> contracts = new HashSet<>();
        for (KeYJavaType type : kjts) {
            if (!KeYTypeUtil.isLibraryClass(type)) {
                SpecificationRepository specRepo = env.getSpecificationRepository();
                for (Contract c : specRepo.getAllContracts()) {
                    var target = c.getTarget();
                    if (target instanceof ProgramMethod pm &&
                            pm.isConstructor() &&
                            !KeYTypeUtil.isLibraryClass(pm.getContainerType())) {
                        contracts.add(c);
                    }
                }
            }
        }
        if (shouldfail)
            return contracts.stream()
                    .map(c -> DynamicTest.dynamicTest("Illegal constructor " + c.getName(),
                        () -> Assertions.assertThrowsExactly(
                            FinalFieldCodeValidator.FinalViolationException.class,
                            () -> testConstructor(c, env))));
        else
            return contracts.stream()
                    .map(c -> DynamicTest.dynamicTest("Legal constructor " + c.getName(),
                        () -> testConstructor(c, env)));
    }

    private void testConstructor(Contract c, KeYEnvironment<?> env)
            throws ProofInputException, MalformedURLException {
        try {
            // System.out.println("Contract id: " + c.getName());
            ContractPO po = c.createProofObl(env.getInitConfig());
            env.createProof(po);
        } catch (FinalFieldCodeValidator.FinalViolationException fex) {
            System.err.println("Position: " + fex.getLocation());
            fex.printStackTrace();
            throw fex;
        }
    }
}
