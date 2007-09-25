package de.uka.ilkd.key.lang.clang.common.programsv;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.sort.ProgramSVSort;

/**
 * ProgramSV sort builder.
 * @author oleg.myrk@gmail.com
 */
public class ProgramSVSortBuilder {
        
        /**
         * Builds a map from ProgramSV sort names to the ProgramSV sorts. 
         * @return
         */
        public static Map buildMap() {
                Map map = new HashMap();
                
                put(map, new IntegerLiteralSort());
                put(map, new VariableSort());
                put(map, new ValueVariableSort());
                put(map, new ObjectVariableSort());
                put(map, new IntegerVariableSort());                
                put(map, new PointerVariableSort());
                put(map, new MemberReferenceSort());
                put(map, new ExpressionSort());
                put(map, new ValueExpressionSort());
                put(map, new IntegerExpressionSort());
                put(map, new PointerExpressionSort());
                put(map, new ObjectExpressionSort());
                put(map, new ValueSimpleExpressionSort());                
                put(map, new IntegerSimpleExpressionSort());
                put(map, new PointerSimpleExpressionSort());                                
                put(map, new ComplexExpressionSort());
                put(map, new ValueComplexExpressionSort());
                put(map, new ObjectComplexExpressionSort());
                put(map, new ValueNonAssignmentExpressionSort());
                put(map, new ObjectNonAssignmentExpressionSort());
                put(map, new ValueTypeSort());
                put(map, new IntegerTypeSort());
                put(map, new PointerTypeSort());
                put(map, new ObjectTypeSort());
                put(map, new ScalarTypeSort());
                put(map, new AggregateTypeSort());
                put(map, new StatementSort());
                put(map, new NonEmptyCompoundStatementSort());
                put(map, new BlockFrameVarDeclSort());
                put(map, new UnwindingBlockFrameSort());
                put(map, new EmptyBlockFrameSort());
                
                return map;
        }
        
        private static void put(Map map, ProgramSVSort sort) {
                map.put(sort.name(), sort);
        }
}
