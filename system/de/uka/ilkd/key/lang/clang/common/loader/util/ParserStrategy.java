package de.uka.ilkd.key.lang.clang.common.loader.util;

import de.uka.ilkd.key.lang.clang.common.programsv.ExpressionProgramSV;
import de.uka.ilkd.key.lang.clang.common.programsv.IExpressionSort;
import de.uka.ilkd.key.lang.clang.common.programsv.IStatementSort;
import de.uka.ilkd.key.lang.clang.common.programsv.ITypeSort;
import de.uka.ilkd.key.lang.clang.common.programsv.IVariableSort;
import de.uka.ilkd.key.lang.clang.common.programsv.MemberReferenceProgramSV;
import de.uka.ilkd.key.lang.clang.common.programsv.MemberReferenceSort;
import de.uka.ilkd.key.lang.clang.common.programsv.StatementProgramSV;
import de.uka.ilkd.key.lang.clang.common.programsv.TypeProgramSV;
import de.uka.ilkd.key.lang.clang.common.programsv.VariableProgramSV;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSV;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;

/**
 * A singleton strategy for C parser needed to resolve schema variables.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ParserStrategy {
        /**
         * Exception thrown when object is not found.
         * 
         * @author oleg.myrk@gmail.com
         */
        public static class NotFoundException extends Exception {
                public NotFoundException(String message) {
                        super(message);
                }
        }

        // TODO: use ThreadLocal instead
        private Namespace schemaVariableNS;

        /**
         * Hidden constructor - use {@link #getInstance} instead.
         */
        private ParserStrategy() {
        }

        /**
         * The singleton instance of the strategy.
         */
        private static ParserStrategy instance = new ParserStrategy();

        /**
         * Returns the single instance of this class.
         */
        public static ParserStrategy getInstance() {
                return (ParserStrategy) instance;
        }

        /**
         * Resets strategy's parameters.
         * 
         * @param schemaVariableNS
         */
        public void reset(Namespace schemaVariableNS) {
                this.schemaVariableNS = schemaVariableNS;
        }

        /**
         * Returns a program schema variable with given name if available.
         * 
         * @param name
         * @return
         * @throws NotFoundException
         */
        public ProgramSV getProgramSV(String name) throws NotFoundException {
                return lookupProgramSV(name);
        }

        /**
         * Tests if a program schema variable with given name is available.
         * 
         * @param name
         * @return
         */
        public boolean testProgramSV(String name) {
                try {
                        getProgramSV(name);
                } catch (NotFoundException e) {
                        return false;
                }
                return true;
        }

        /**
         * Returns a type program schema variable with given name if available.
         * 
         * @param name
         * @return
         * @throws NotFoundException
         */
        public TypeSVWrapper getTypeSV(String name) throws NotFoundException {
                TypeProgramSV sv = (TypeProgramSV) lookupSchemaVariable(name,
                                ITypeSort.class, "Type");
                return new TypeSVWrapper(sv);
        }

        /**
         * Tests if a type program schema variable with given name is available.
         * 
         * @param name
         * @return
         */
        public boolean testTypeSV(String name) {
                try {
                        getTypeSV(name);
                } catch (NotFoundException e) {
                        return false;
                }
                return true;
        }

        /**
         * Returns a type program schema variable with given name if available.
         * 
         * @param name
         * @return
         * @throws NotFoundException
         */
        public VariableSVWrapper getVariableSV(String name)
                        throws NotFoundException {
                VariableProgramSV sv = (VariableProgramSV) lookupSchemaVariable(
                                name, IVariableSort.class, "Variable");
                return new VariableSVWrapper(sv);
        }

        /**
         * Tests if a variable program schema variable with given name is
         * available.
         * 
         * @param name
         * @return
         */
        public boolean testVariableSV(String name) {
                try {
                        getVariableSV(name);
                } catch (NotFoundException e) {
                        return false;
                }
                return true;
        }

        /**
         * Returns a member program schema variable with given name if
         * available.
         * 
         * @param name
         * @return
         * @throws NotFoundException
         */
        public MemberSVWrapper getMemberSV(String name)
                        throws NotFoundException {
                MemberReferenceProgramSV sv = (MemberReferenceProgramSV) lookupSchemaVariable(
                                name, MemberReferenceSort.class, "Member");
                return new MemberSVWrapper(sv);
        }

        /**
         * Tests if a member program schema variable with given name is
         * available.
         * 
         * @param name
         * @return
         */
        public boolean testMemberSV(String name) {
                try {
                        getMemberSV(name);
                } catch (NotFoundException e) {
                        return false;
                }
                return true;
        }

        /**
         * Returns a statement program schema variable with given name if
         * available.
         * 
         * @param name
         * @return
         * @throws NotFoundException
         */
        public StatementSVWrapper getStatementSV(String name)
                        throws NotFoundException {
                StatementProgramSV sv = (StatementProgramSV) lookupSchemaVariable(
                                name, IStatementSort.class, "Statement");
                return new StatementSVWrapper(sv);
        }

        /**
         * Tests if a statement program schema variable with given name is
         * available.
         * 
         * @param name
         * @return
         */
        public boolean testStatementSV(String name) {
                try {
                        getStatementSV(name);
                } catch (NotFoundException e) {
                        return false;
                }
                return true;
        }

        /**
         * Returns an expression program schema variable with given name if
         * available.
         * 
         * @param name
         * @return
         * @throws NotFoundException
         */
        public ExpressionSVWrapper getExpressionSV(String name)
                        throws NotFoundException {
                ExpressionProgramSV sv = (ExpressionProgramSV) lookupSchemaVariable(
                                name, new Class[] {
                                                IExpressionSort.class,
                                                ProgramSVSort.VARIABLE
                                                                .getClass() },
                                "Expression");
                return new ExpressionSVWrapper(sv);
        }

        /**
         * Tests if an expression program schema variable with given name is
         * available.
         * 
         * @param name
         * @return
         */
        public boolean testExpressionSV(String name) {
                try {
                        getExpressionSV(name);
                } catch (NotFoundException e) {
                        return false;
                }
                return true;
        }

        /**
         * Looks up schema variable with given name and a super class of sort.
         * Sort name is used for error messages.
         * 
         * @param name
         * @param sortSuperClass
         * @param sortName
         * @return
         * @throws NotFoundException
         */
        private BaseProgramSV lookupSchemaVariable(String name,
                        Class sortSuperClass, String sortName)
                        throws NotFoundException {
                return lookupSchemaVariable(name,
                                new Class[] { sortSuperClass }, sortName);
        }

        /**
         * Looks up schema variable with given name and a sort that extends one
         * of the super classes. Sort name is used for error messages.
         * 
         * @param name
         * @param sortSuperClasses
         * @param sortName
         * @return
         * @throws NotFoundException
         */
        private BaseProgramSV lookupSchemaVariable(String name,
                        Class[] sortSuperClasses, String sortName)
                        throws NotFoundException {
                BaseProgramSV programSV = lookupProgramSV(name);
                boolean found = false;
                for (int i = 0; i < sortSuperClasses.length; i++) {
                        if (sortSuperClasses[i].isAssignableFrom(programSV
                                        .sort(new Term[0]).getClass()))
                                found = true;
                }
                if (!found)
                        throw new NotFoundException(
                                        "Sort of declared schema variable "
                                                        + programSV.name()
                                                        + " "
                                                        + (programSV).sort()
                                                                        .name()
                                                        + " does not comply with expected type "
                                                        + sortName
                                                        + " in program.");
                return programSV;
        }

        /**
         * Looks up program schema variable by its name.
         * 
         * @param name
         * @return
         * @throws NotFoundException
         */
        private BaseProgramSV lookupProgramSV(String name)
                        throws NotFoundException {
                Named named = schemaVariableNS.lookup(new Name(name));
                if (named == null) {
                        throw new NotFoundException(
                                        "Schema variable not declared: " + name);
                } else if (!(named instanceof ProgramSV)) {
                        throw new NotFoundException(
                                        "Schema variable is not a program schema variable: "
                                                        + name);
                }
                return (BaseProgramSV) named;
        }
}
