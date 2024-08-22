package org.key_project.rusty;

import org.junit.jupiter.api.Test;
import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.rusty.ast.SchemaRustyReader;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.logic.op.sv.SchemaVariableFactory;
import org.key_project.rusty.logic.sort.ProgramSVSort;
import org.key_project.rusty.util.TacletForTests;

public class TestSchemaParser {
    @Test
    void testSimpleParse() {
        var services = TacletForTests.services();
        var nss = TacletForTests.nss;
        var rr = new SchemaRustyReader(services,nss);
        var svNS = new Namespace<SchemaVariable>();
        svNS.add(SchemaVariableFactory.createProgramSV(new Name("loc"), ProgramSVSort.VARIABLE, false));
        svNS.add(SchemaVariableFactory.createProgramSV(new Name("se"), ProgramSVSort.SIMPLE_EXPRESSION, false));
        rr.setSVNamespace(svNS);
        var parsed = rr.readBlockWithEmptyContext("{c# #c}");
        System.out.println(parsed);
    }
}
