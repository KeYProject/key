/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.transformation;

import java.io.File;
import java.io.IOException;
import java.util.List;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.io.DefaultSourceFileRepository;
import recoder.io.PropertyNames;
import recoder.java.Identifier;
import recoder.java.StatementBlock;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.modifier.Private;
import recoder.java.declaration.modifier.Public;
import recoder.java.declaration.modifier.VisibilityModifier;
import recoder.java.reference.TypeReference;
import recoder.service.ChangeHistory;
import recoder.service.NameInfo;

import static org.junit.jupiter.api.Assertions.fail;
// import application.Obfuscate;


/**
 * @author gutzmann
 *         <p>
 *         Tests some transformations.
 */
@Disabled
public class TransformationTests {
    private CrossReferenceServiceConfiguration crsc;
    private DefaultSourceFileRepository dsfr;
    private final boolean silent = true;

    private void setPath(String base) {
        crsc = new CrossReferenceServiceConfiguration();
        dsfr = new DefaultSourceFileRepository(crsc);
        crsc.getProjectSettings().addPropertyChangeListener(dsfr);
        crsc.getProjectSettings().setProperty(PropertyNames.INPUT_PATH,
            new File("src/test/resources/transformation/" + base + "/").getAbsolutePath());
        crsc.getProjectSettings().setProperty(PropertyNames.OUTPUT_PATH,
            new File("build/tmp/transformation/output/" + base + "/").getAbsolutePath());
        crsc.getProjectSettings().ensureSystemClassesAreInPath();
        dsfr.initialize(crsc);
    }

    private void runIt() {
        try {
            dsfr.getAllCompilationUnitsFromPath();
            crsc.getChangeHistory().updateModel();
        } catch (ParserException pe) {
            System.err.println(pe.getMessage());
            fail("unexpected ParserException");
        }
    }

    private void writeBack() {
        try {
            dsfr.printAll(true);
        } catch (IOException e) {
            fail();
        }
    }

    /*
     * public void testObfuscater() { setPath("obfuscate"); runIt(); Obfuscate of = new
     * Obfuscate(crsc); if (of.analyze() instanceof NoProblem) of.transform(); // TODO write back
     * and compare! }
     */

    @Test
    public void testReadOnly() {
        setPath("readOnly");
        runIt();

        List<TypeReference> trl =
            crsc.getCrossReferenceSourceInfo().getReferences(crsc.getNameInfo().getType("Test"));
        for (TypeReference tr : trl) {
            System.out.println(tr.toSource());
        }
    }

    private void defaultConstructorReferences(VisibilityModifier vm) {
        setPath("defaultCons");
        runIt();
        // add a constructor now
        ChangeHistory ch = crsc.getChangeHistory();
        NameInfo ni = crsc.getNameInfo();
        ClassDeclaration cd = (ClassDeclaration) ni.getType("DefaultCons");
        ConstructorDeclaration cons = new ConstructorDeclaration(vm, new Identifier("DefaultCons"),
            null, null, new StatementBlock());
        cd.getMembers().add(cons);
        cd.makeParentRoleValid();
        ch.attached(cons);
        ch.updateModel();
        // now, the default constructor no longer exists.
        // The added constructor should be referenced, however, if it is still visible,
        // and an error should occur if not.
        // TODO Recoder does not check visibility yet! So this works fine for both cases (for now)!

        int newref = crsc.getCrossReferenceSourceInfo().getReferences(cons).size();
        System.out.println(newref);

        cd.getMethods().get(0);
    }

    @Test
    public void testDefaultConstructorReferences1() {
        defaultConstructorReferences(new Public());
    }

    @Test
    public void testDefaultConstructorReferences2() {
        defaultConstructorReferences(new Private());
    }
}
