/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

/**
 * Stub AST node classes for remaining KeY grammar constructs.
 * These are placeholder implementations that can be expanded as needed.
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public class StubAstNodes {

    // ==================== Declaration Stubs ====================

    /** Include statement declaration */
    public static class IncludeStatement extends BaseAstNode implements Declaration {
        private final boolean isLDTs;
        private final List<OneInclude> includes;

        public IncludeStatement(Position position,
                                boolean isLDTs, List<OneInclude> includes) {
            super(position);
            this.isLDTs = isLDTs;
            this.includes = includes;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public boolean isLDTs() { return isLDTs; }
        public List<OneInclude> getIncludes() { return includes; }
    }

    public static class OneInclude extends BaseAstNode {
        private final @Nullable String absFile;
        private final @Nullable String relFile;

        public OneInclude(Position position,
                          @Nullable String absFile, @Nullable String relFile) {
            super(position);
            this.absFile = absFile;
            this.relFile = relFile;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public @Nullable String getAbsFile() { return absFile; }
        public @Nullable String getRelFile() { return relFile; }
    }

    /** Options choice declaration */
    public static class OptionsChoice extends BaseAstNode implements Declaration {
        private final List<ActivatedChoice> choices;

        public OptionsChoice(Position position,
                             List<ActivatedChoice> choices) {
            super(position);
            this.choices = choices;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<ActivatedChoice> getChoices() { return choices; }
    }

    public static class ActivatedChoice extends BaseAstNode {
        private final String category;
        private final String choice;

        public ActivatedChoice(Position position,
                               String category, String choice) {
            super(position);
            this.category = category;
            this.choice = choice;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public String getCategory() { return category; }
        public String getChoice() { return choice; }
    }

    /** Option declarations */
    public static class OptionDecls extends BaseAstNode implements Declaration {
        private final List<Choice> choices;

        public OptionDecls(Position position,
                           List<Choice> choices) {
            super(position);
            this.choices = choices;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<Choice> getChoices() { return choices; }
    }

    public static class Choice extends BaseAstNode {
        private final List<String> docComments;
        private final String category;
        private final List<OptionDecl> options;

        public Choice(Position position,
                      List<String> docComments, String category, List<OptionDecl> options) {
            super(position);
            this.docComments = docComments;
            this.category = category;
            this.options = options;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<String> getDocComments() { return docComments; }
        public String getCategory() { return category; }
        public List<OptionDecl> getOptions() { return options; }
    }

    public static class OptionDecl extends BaseAstNode {
        private final @Nullable String docComment;
        private final List<String> choices;

        public OptionDecl(Position position,
                          @Nullable String docComment, List<String> choices) {
            super(position);
            this.docComment = docComment;
            this.choices = choices;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public @Nullable String getDocComment() { return docComment; }
        public List<String> getChoices() { return choices; }
    }

    /** Sort declarations */
    public static class SortDecls extends BaseAstNode implements Declaration {
        private final List<OneSortDecl> sorts;

        public SortDecls(Position position,
                         List<OneSortDecl> sorts) {
            super(position);
            this.sorts = sorts;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<OneSortDecl> getSorts() { return sorts; }
    }

    public static class OneSortDecl extends BaseAstNode {
        public enum SortKind { GENERIC, PROXY, ABSTRACT, ALIAS }
        private final SortKind kind;
        private final @Nullable String docComment;
        private final List<String> sortIds;
        private final @Nullable String extendsSorts;
        private final @Nullable String aliasTarget;

        public OneSortDecl(Position position,
                           SortKind kind, @Nullable String docComment, List<String> sortIds,
                           @Nullable String extendsSorts, @Nullable String aliasTarget) {
            super(position);
            this.kind = kind;
            this.docComment = docComment;
            this.sortIds = sortIds;
            this.extendsSorts = extendsSorts;
            this.aliasTarget = aliasTarget;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public SortKind getKind() { return kind; }
        public @Nullable String getDocComment() { return docComment; }
        public List<String> getSortIds() { return sortIds; }
        public @Nullable String getExtendsSorts() { return extendsSorts; }
        public @Nullable String getAliasTarget() { return aliasTarget; }
    }

    /** Program variable declarations */
    public static class ProgVarDecls extends BaseAstNode implements Declaration {
        private final List<ProgVarDecl> variables;

        public ProgVarDecls(Position position,
                            List<ProgVarDecl> variables) {
            super(position);
            this.variables = variables;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<ProgVarDecl> getVariables() { return variables; }
    }

    public static class ProgVarDecl extends BaseAstNode {
        private final String type;
        private final List<String> names;

        public ProgVarDecl(Position position,
                           String type, List<String> names) {
            super(position);
            this.type = type;
            this.names = names;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public String getType() { return type; }
        public List<String> getNames() { return names; }
    }

    /** Schema variable declarations */
    public static class SchemaVarDecls extends BaseAstNode implements Declaration {
        private final List<OneSchemaVarDecl> schemaVars;

        public SchemaVarDecls(Position position,
                              List<OneSchemaVarDecl> schemaVars) {
            super(position);
            this.schemaVars = schemaVars;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<OneSchemaVarDecl> getSchemaVars() { return schemaVars; }
    }

    public static class OneSchemaVarDecl extends BaseAstNode {
        public enum SchemaKind { MODAL_OPERATOR, PROGRAM, FORMULA, TERMLABEL, UPDATE, SKOLEM_FORMULA, TERM_VAR }
        private final SchemaKind kind;
        private final String name;
        private final @Nullable SortId sort;

        public OneSchemaVarDecl(Position position,
                                SchemaKind kind, String name, @Nullable SortId sort) {
            super(position);
            this.kind = kind;
            this.name = name;
            this.sort = sort;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public SchemaKind getKind() { return kind; }
        public String getName() { return name; }
        public @Nullable SortId getSort() { return sort; }
    }

    public static class SchemaModifiers extends BaseAstNode {
        private final List<String> options;

        public SchemaModifiers(Position position,
                               List<String> options) {
            super(position);
            this.options = options;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<String> getOptions() { return options; }
    }

    /** Predicate declarations */
    public static class PredDecls extends BaseAstNode implements Declaration {
        private final List<PredDecl> predicates;

        public PredDecls(Position position,
                         List<PredDecl> predicates) {
            super(position);
            this.predicates = predicates;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<PredDecl> getPredicates() { return predicates; }
    }

    public static class PredDecl extends BaseAstNode {
        private final @Nullable String docComment;
        private final String name;
        private final List<SortId> argSorts;

        public PredDecl(Position position,
                        @Nullable String docComment, String name, List<SortId> argSorts) {
            super(position);
            this.docComment = docComment;
            this.name = name;
            this.argSorts = argSorts;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public @Nullable String getDocComment() { return docComment; }
        public String getName() { return name; }
        public List<SortId> getArgSorts() { return argSorts; }
    }

    /** Function declarations */
    public static class FuncDecls extends BaseAstNode implements Declaration {
        private final List<FuncDecl> functions;

        public FuncDecls(Position position,
                         List<FuncDecl> functions) {
            super(position);
            this.functions = functions;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<FuncDecl> getFunctions() { return functions; }
    }

    public static class FuncDecl extends BaseAstNode {
        private final @Nullable String docComment;
        private final boolean unique;
        private final SortId returnType;
        private final String name;
        private final List<SortId> argSorts;

        public FuncDecl(Position position,
                        @Nullable String docComment, boolean unique, SortId returnType,
                        String name, List<SortId> argSorts) {
            super(position);
            this.docComment = docComment;
            this.unique = unique;
            this.returnType = returnType;
            this.name = name;
            this.argSorts = argSorts;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public @Nullable String getDocComment() { return docComment; }
        public boolean isUnique() { return unique; }
        public SortId getReturnType() { return returnType; }
        public String getName() { return name; }
        public List<SortId> getArgSorts() { return argSorts; }
    }

    /** Transform declarations */
    public static class TransformDecls extends BaseAstNode implements Declaration {
        private final List<TransformDecl> transforms;

        public TransformDecls(Position position,
                              List<TransformDecl> transforms) {
            super(position);
            this.transforms = transforms;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<TransformDecl> getTransforms() { return transforms; }
    }

    public static class TransformDecl extends BaseAstNode {
        private final @Nullable String docComment;
        private final @Nullable SortId returnType;
        private final boolean returnsFormula;
        private final String name;
        private final List<Object> argSorts;

        public TransformDecl(Position position,
                             @Nullable String docComment, @Nullable SortId returnType,
                             boolean returnsFormula, String name, List<Object> argSorts) {
            super(position);
            this.docComment = docComment;
            this.returnType = returnType;
            this.returnsFormula = returnsFormula;
            this.name = name;
            this.argSorts = argSorts;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public @Nullable String getDocComment() { return docComment; }
        public @Nullable SortId getReturnType() { return returnType; }
        public boolean returnsFormula() { return returnsFormula; }
        public String getName() { return name; }
        public List<Object> getArgSorts() { return argSorts; }
    }

    /** Datatype declarations */
    public static class DatatypeDecls extends BaseAstNode implements Declaration {
        private final List<DatatypeDecl> datatypes;

        public DatatypeDecls(Position position,
                             List<DatatypeDecl> datatypes) {
            super(position);
            this.datatypes = datatypes;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<DatatypeDecl> getDatatypes() { return datatypes; }
    }

    public static class DatatypeDecl extends BaseAstNode {
        private final @Nullable String docComment;
        private final String name;
        private final List<DatatypeConstructor> constructors;

        public DatatypeDecl(Position position,
                            @Nullable String docComment, String name,
                            List<DatatypeConstructor> constructors) {
            super(position);
            this.docComment = docComment;
            this.name = name;
            this.constructors = constructors;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public @Nullable String getDocComment() { return docComment; }
        public String getName() { return name; }
        public List<DatatypeConstructor> getConstructors() { return constructors; }
    }

    public static class DatatypeConstructor extends BaseAstNode {
        private final String name;
        private final List<String> argSorts;
        private final List<String> argNames;

        public DatatypeConstructor(Position position,
                                   String name, List<String> argSorts, List<String> argNames) {
            super(position);
            this.name = name;
            this.argSorts = argSorts;
            this.argNames = argNames;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public String getName() { return name; }
        public List<String> getArgSorts() { return argSorts; }
        public List<String> getArgNames() { return argNames; }
    }

    /** Ruleset declarations */
    public static class RulesetDecls extends BaseAstNode implements Declaration {
        private final List<String> rulesets;

        public RulesetDecls(Position position,
                            List<String> rulesets) {
            super(position);
            this.rulesets = rulesets;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<String> getRulesets() { return rulesets; }
    }

    /** Contracts */
    public static class Contracts extends BaseAstNode implements Declaration {
        private final List<OneContract> contracts;

        public Contracts(Position position,
                         List<OneContract> contracts) {
            super(position);
            this.contracts = contracts;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<OneContract> getContracts() { return contracts; }
    }

    /** Invariants */
    public static class Invariants extends BaseAstNode implements Declaration {
        private final OneBoundVariable selfVar;
        private final List<OneInvariant> invariants;

        public Invariants(Position position,
                          OneBoundVariable selfVar, List<OneInvariant> invariants) {
            super(position);
            this.selfVar = selfVar;
            this.invariants = invariants;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public OneBoundVariable getSelfVar() { return selfVar; }
        public List<OneInvariant> getInvariants() { return invariants; }
    }

    /** Rules or Axioms */
    public static class RulesOrAxioms extends BaseAstNode implements Declaration {
        private final @Nullable String docComment;
        private final boolean isRules;
        private final @Nullable OptionList options;
        private final List<Taclet> taclets;

        public RulesOrAxioms(Position position,
                             @Nullable String docComment, boolean isRules,
                             @Nullable OptionList options, List<Taclet> taclets) {
            super(position);
            this.docComment = docComment;
            this.isRules = isRules;
            this.options = options;
            this.taclets = taclets;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public @Nullable String getDocComment() { return docComment; }
        public boolean isRules() { return isRules; }
        public @Nullable OptionList getOptions() { return options; }
        public List<Taclet> getTaclets() { return taclets; }
    }

    // ==================== Taclet Support Classes ====================


    public static class OptionExpr extends BaseAstNode {
        public enum OpKind { AND, OR, NOT, PROP }
        private final OpKind kind;
        private final @Nullable OptionExpr left;
        private final @Nullable OptionExpr right;
        private final @Nullable String propCategory;
        private final @Nullable String propValue;

        public OptionExpr(Position position,
                          OpKind kind, @Nullable OptionExpr left, @Nullable OptionExpr right,
                          @Nullable String propCategory, @Nullable String propValue) {
            super(position);
            this.kind = kind;
            this.left = left;
            this.right = right;
            this.propCategory = propCategory;
            this.propValue = propValue;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public OpKind getKind() { return kind; }
        public @Nullable OptionExpr getLeft() { return left; }
        public @Nullable OptionExpr getRight() { return right; }
        public @Nullable String getPropCategory() { return propCategory; }
        public @Nullable String getPropValue() { return propValue; }
    }

    public static class Seq extends BaseAstNode {
        private final SemiSequent antecedent;
        private final SemiSequent succedent;

        public Seq(Position position,
                   SemiSequent antecedent, SemiSequent succedent) {
            super(position);
            this.antecedent = antecedent;
            this.succedent = succedent;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public SemiSequent getAntecedent() { return antecedent; }
        public SemiSequent getSuccedent() { return succedent; }
    }

    public static class TermOrSeq extends BaseAstNode {
        private final @Nullable Term term;
        private final @Nullable Seq seq;

        public TermOrSeq(Position position,
                         @Nullable Term term, @Nullable Seq seq) {
            super(position);
            this.term = term;
            this.seq = seq;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public @Nullable Term getTerm() { return term; }
        public @Nullable Seq getSeq() { return seq; }
    }

    public static class SemiSequent extends BaseAstNode {
        private final List<Term> terms;

        public SemiSequent(Position position,
                           List<Term> terms) {
            super(position);
            this.terms = terms;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<Term> getTerms() { return terms; }
    }

    public static class GoalSpecs extends BaseAstNode {
        private final boolean closeGoal;
        private final List<GoalSpecWithOption> specs;

        public GoalSpecs(Position position,
                         boolean closeGoal, List<GoalSpecWithOption> specs) {
            super(position);
            this.closeGoal = closeGoal;
            this.specs = specs;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public boolean isCloseGoal() { return closeGoal; }
        public List<GoalSpecWithOption> getSpecs() { return specs; }
    }

    public static class GoalSpecWithOption extends BaseAstNode {
        private final @Nullable OptionList options;
        private final GoalSpec spec;

        public GoalSpecWithOption(Position position,
                                  @Nullable OptionList options, GoalSpec spec) {
            super(position);
            this.options = options;
            this.spec = spec;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public @Nullable OptionList getOptions() { return options; }
        public GoalSpec getSpec() { return spec; }
    }

    public static class GoalSpec extends BaseAstNode {
        private final @Nullable String name;
        private final @Nullable String tag;
        private final @Nullable ReplaceWith replaceWith;
        private final @Nullable Add add;
        private final @Nullable AddRules addRules;
        private final @Nullable AddProgVars addProgVars;

        public GoalSpec(Position position,
                        @Nullable String name, @Nullable String tag,
                        @Nullable ReplaceWith replaceWith, @Nullable Add add,
                        @Nullable AddRules addRules, @Nullable AddProgVars addProgVars) {
            super(position);
            this.name = name;
            this.tag = tag;
            this.replaceWith = replaceWith;
            this.add = add;
            this.addRules = addRules;
            this.addProgVars = addProgVars;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public @Nullable String getName() { return name; }
        public @Nullable String getTag() { return tag; }
        public @Nullable ReplaceWith getReplaceWith() { return replaceWith; }
        public @Nullable Add getAdd() { return add; }
        public @Nullable AddRules getAddRules() { return addRules; }
        public @Nullable AddProgVars getAddProgVars() { return addProgVars; }
    }

    public static class ReplaceWith extends BaseAstNode {
        private final TermOrSeq termOrSeq;

        public ReplaceWith(Position position,
                           TermOrSeq termOrSeq) {
            super(position);
            this.termOrSeq = termOrSeq;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public TermOrSeq getTermOrSeq() { return termOrSeq; }
    }

    public static class Add extends BaseAstNode {
        private final Seq seq;

        public Add(Position position, Seq seq) {
            super(position);
            this.seq = seq;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public Seq getSeq() { return seq; }
    }

    public static class AddRules extends BaseAstNode {
        private final List<Taclet> taclets;

        public AddRules(Position position,
                        List<Taclet> taclets) {
            super(position);
            this.taclets = taclets;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<Taclet> getTaclets() { return taclets; }
    }

    public static class AddProgVars extends BaseAstNode {
        private final List<String> varIds;

        public AddProgVars(Position position,
                           List<String> varIds) {
            super(position);
            this.varIds = varIds;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<String> getVarIds() { return varIds; }
    }

    public static class Modifiers extends BaseAstNode {
        private final List<String> rulesets;
        private final boolean nonInteractive;
        private final @Nullable String displayName;
        private final @Nullable String helpText;
        private final @Nullable Triggers triggers;

        public Modifiers(Position position,
                         List<String> rulesets, boolean nonInteractive,
                         @Nullable String displayName, @Nullable String helpText,
                         @Nullable Triggers triggers) {
            super(position);
            this.rulesets = rulesets;
            this.nonInteractive = nonInteractive;
            this.displayName = displayName;
            this.helpText = helpText;
            this.triggers = triggers;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<String> getRulesets() { return rulesets; }
        public boolean isNonInteractive() { return nonInteractive; }
        public @Nullable String getDisplayName() { return displayName; }
        public @Nullable String getHelpText() { return helpText; }
        public @Nullable Triggers getTriggers() { return triggers; }
    }

    public static class Triggers extends BaseAstNode {
        private final String id;
        private final Term triggerTerm;
        private final List<Term> avoidTerms;

        public Triggers(Position position,
                        String id, Term triggerTerm, List<Term> avoidTerms) {
            super(position);
            this.id = id;
            this.triggerTerm = triggerTerm;
            this.avoidTerms = avoidTerms;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public String getId() { return id; }
        public Term getTriggerTerm() { return triggerTerm; }
        public List<Term> getAvoidTerms() { return avoidTerms; }
    }

    public static class VarexpList extends BaseAstNode {
        private final List<Varexp> varexps;

        public VarexpList(Position position,
                          List<Varexp> varexps) {
            super(position);
            this.varexps = varexps;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<Varexp> getVarexps() { return varexps; }
    }

    public static class Varexp extends BaseAstNode {
        private final boolean negated;
        private final String varExpId;
        private final List<String> parameters;
        private final List<Object> arguments;

        public Varexp(Position position,
                      boolean negated, String varExpId, List<String> parameters,
                      List<Object> arguments) {
            super(position);
            this.negated = negated;
            this.varExpId = varExpId;
            this.parameters = parameters;
            this.arguments = arguments;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public boolean isNegated() { return negated; }
        public String getVarExpId() { return varExpId; }
        public List<String> getParameters() { return parameters; }
        public List<Object> getArguments() { return arguments; }
    }


    // ==================== Term Support Classes ====================

    public static class Label extends BaseAstNode {
        private final List<SingleLabel> labels;

        public Label(Position position,
                     List<SingleLabel> labels) {
            super(position);
            this.labels = labels;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<SingleLabel> getLabels() { return labels; }
    }

    public static class SingleLabel extends BaseAstNode {
        private final @Nullable String name;
        private final boolean isStar;
        private final List<String> params;

        public SingleLabel(Position position,
                           @Nullable String name, boolean isStar, List<String> params) {
            super(position);
            this.name = name;
            this.isStar = isStar;
            this.params = params;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public @Nullable String getName() { return name; }
        public boolean isStar() { return isStar; }
        public List<String> getParams() { return params; }
    }

    public static class LocsetTerm extends BaseAstNode {
        private final List<LocationTerm> locations;

        public LocsetTerm(Position position,
                          List<LocationTerm> locations) {
            super(position);
            this.locations = locations;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<LocationTerm> getLocations() { return locations; }
    }

    public static class LocationTerm extends BaseAstNode {
        private final Term obj;
        private final Term field;

        public LocationTerm(Position position,
                            Term obj, Term field) {
            super(position);
            this.obj = obj;
            this.field = field;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public Term getObj() { return obj; }
        public Term getField() { return field; }
    }

    public static class AccessTerm extends BaseAstNode {
        private final @Nullable SortId qualifier;
        private final String firstName;
        private final @Nullable FormalSortArgs formalArgs;
        private final @Nullable Call call;
        private final List<Attribute> attributes;

        public AccessTerm(Position position,
                          @Nullable SortId qualifier, String firstName,
                          @Nullable FormalSortArgs formalArgs, @Nullable Call call,
                          List<Attribute> attributes) {
            super(position);
            this.qualifier = qualifier;
            this.firstName = firstName;
            this.formalArgs = formalArgs;
            this.call = call;
            this.attributes = attributes;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public @Nullable SortId getQualifier() { return qualifier; }
        public String getFirstName() { return firstName; }
        public @Nullable FormalSortArgs getFormalArgs() { return formalArgs; }
        public @Nullable Call getCall() { return call; }
        public List<Attribute> getAttributes() { return attributes; }
    }

    public static class Call extends BaseAstNode {
        private final @Nullable BoundVariables boundVars;
        private final List<Term> args;

        public Call(Position position,
                    @Nullable BoundVariables boundVars, List<Term> args) {
            super(position);
            this.boundVars = boundVars;
            this.args = args;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public @Nullable BoundVariables getBoundVars() { return boundVars; }
        public List<Term> getArgs() { return args; }
    }

    public static class Attribute extends BaseAstNode {
        public enum AttrKind { STAR, SIMPLE, COMPLEX }
        private final AttrKind kind;
        private final @Nullable String id;
        private final @Nullable SortId sort;
        private final @Nullable Call call;
        private final @Nullable BracketTerm heap;

        public Attribute(Position position,
                         AttrKind kind, @Nullable String id, @Nullable SortId sort,
                         @Nullable Call call, @Nullable BracketTerm heap) {
            super(position);
            this.kind = kind;
            this.id = id;
            this.sort = sort;
            this.call = call;
            this.heap = heap;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public AttrKind getKind() { return kind; }
        public @Nullable String getId() { return id; }
        public @Nullable SortId getSort() { return sort; }
        public @Nullable Call getCall() { return call; }
        public @Nullable BracketTerm getHeap() { return heap; }
    }

    public static class Abbreviation extends BaseAstNode {
        private final String name;

        public Abbreviation(Position position,
                            String name) {
            super(position);
            this.name = name;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public String getName() { return name; }
    }

    public static class IfThenElseTerm extends BaseAstNode {
        private final Term cond;
        private final Term thenT;
        private final Term elseT;

        public IfThenElseTerm(Position position,
                              Term cond, Term thenT, Term elseT) {
            super(position);
            this.cond = cond;
            this.thenT = thenT;
            this.elseT = elseT;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public Term getCond() { return cond; }
        public Term getThenT() { return thenT; }
        public Term getElseT() { return elseT; }
    }

    public static class IfExThenElseTerm extends BaseAstNode {
        private final BoundVariables exVars;
        private final Term cond;
        private final Term thenT;
        private final Term elseT;

        public IfExThenElseTerm(Position position,
                                BoundVariables exVars, Term cond, Term thenT, Term elseT) {
            super(position);
            this.exVars = exVars;
            this.cond = cond;
            this.thenT = thenT;
            this.elseT = elseT;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public BoundVariables getExVars() { return exVars; }
        public Term getCond() { return cond; }
        public Term getThenT() { return thenT; }
        public Term getElseT() { return elseT; }
    }

    public static class BracketTerm extends BaseAstNode {
        private final Term primitive;
        private final List<BracketSuffixHeap> suffixes;
        private final List<Attribute> attributes;

        public BracketTerm(Position position,
                           Term primitive, List<BracketSuffixHeap> suffixes,
                           List<Attribute> attributes) {
            super(position);
            this.primitive = primitive;
            this.suffixes = suffixes;
            this.attributes = attributes;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public Term getPrimitive() { return primitive; }
        public List<BracketSuffixHeap> getSuffixes() { return suffixes; }
        public List<Attribute> getAttributes() { return attributes; }
    }

    public static class BracketSuffixHeap extends BaseAstNode {
        private final BraceSuffix braceSuffix;
        private final @Nullable BracketTerm heap;

        public BracketSuffixHeap(Position position,
                                 BraceSuffix braceSuffix, @Nullable BracketTerm heap) {
            super(position);
            this.braceSuffix = braceSuffix;
            this.heap = heap;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public BraceSuffix getBraceSuffix() { return braceSuffix; }
        public @Nullable BracketTerm getHeap() { return heap; }
    }

    public static class BraceSuffix extends BaseAstNode {
        public enum SuffixKind { UPDATE, CALL, STAR, INDEX }
        private final SuffixKind kind;
        private final @Nullable Term target;
        private final @Nullable Term value;
        private final @Nullable String id;
        private final List<Term> args;
        private final @Nullable Term indexTerm;
        private final @Nullable Term rangeTo;

        public BraceSuffix(Position position,
                           SuffixKind kind, @Nullable Term target, @Nullable Term value,
                           @Nullable String id, List<Term> args,
                           @Nullable Term indexTerm, @Nullable Term rangeTo) {
            super(position);
            this.kind = kind;
            this.target = target;
            this.value = value;
            this.id = id;
            this.args = args;
            this.indexTerm = indexTerm;
            this.rangeTo = rangeTo;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public SuffixKind getKind() { return kind; }
        public @Nullable Term getTarget() { return target; }
        public @Nullable Term getValue() { return value; }
        public @Nullable String getId() { return id; }
        public List<Term> getArgs() { return args; }
        public @Nullable Term getIndexTerm() { return indexTerm; }
        public @Nullable Term getRangeTo() { return rangeTo; }
    }

    // ==================== Proof Script Classes ====================

    public static class ProofScript extends BaseAstNode {
        private final List<ProofScriptCommand> commands;

        public ProofScript(Position position,
                           List<ProofScriptCommand> commands) {
            super(position);
            this.commands = commands;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<ProofScriptCommand> getCommands() { return commands; }
    }

    public static class ProofScriptCommand extends BaseAstNode {
        private final String cmd;
        private final List<ProofScriptParameter> parameters;

        public ProofScriptCommand(Position position,
                                  String cmd, List<ProofScriptParameter> parameters) {
            super(position);
            this.cmd = cmd;
            this.parameters = parameters;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public String getCmd() { return cmd; }
        public List<ProofScriptParameter> getParameters() { return parameters; }
    }

    // ==================== Configuration Classes ====================

    public static class ConfigurationFile extends BaseAstNode {
        private final List<CValue> values;

        public ConfigurationFile(Position position,
                                 List<CValue> values) {
            super(position);
            this.values = values;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public List<CValue> getValues() { return values; }
    }

    public static class CKV extends BaseAstNode {
        private final @Nullable String docComment;
        private final CKey key;
        private final CValue value;

        public CKV(Position position,
                   @Nullable String docComment, CKey key, CValue value) {
            super(position);
            this.docComment = docComment;
            this.key = key;
            this.value = value;
        }

        @Override
        public <T> T accept(AstVisitor<T> visitor) {
            return visitor.visit(this);
        }

        public @Nullable String getDocComment() { return docComment; }
        public CKey getKey() { return key; }
        public CValue getValue() { return value; }
    }
}
