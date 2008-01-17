package de.uka.ilkd.key.lang.clang.common.loader;

import java.io.BufferedInputStream;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.lang.reflect.Field;
import java.math.BigInteger;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import cetus.hir.TranslationUnit;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.iface.IClangPlatform;
import de.uka.ilkd.key.lang.clang.common.loader.parser.CLexer;
import de.uka.ilkd.key.lang.clang.common.loader.parser.CParser;
import de.uka.ilkd.key.lang.clang.common.loader.parser.PreprocessorInfoChannel;
import de.uka.ilkd.key.lang.clang.common.loader.parser.SchemaCLexer;
import de.uka.ilkd.key.lang.clang.common.loader.parser.SchemaCParser;
import de.uka.ilkd.key.lang.clang.common.loader.util.ExpressionSVWrapper;
import de.uka.ilkd.key.lang.clang.common.loader.util.MemberSVWrapper;
import de.uka.ilkd.key.lang.clang.common.loader.util.ParserStrategy;
import de.uka.ilkd.key.lang.clang.common.loader.util.StatementSVWrapper;
import de.uka.ilkd.key.lang.clang.common.loader.util.TypeSVWrapper;
import de.uka.ilkd.key.lang.clang.common.loader.util.VariableSVWrapper;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.iface.ArrayOfIClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangVariable;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangVariable;
import de.uka.ilkd.key.lang.clang.common.program.statement.ListOfIStatement;
import de.uka.ilkd.key.lang.clang.common.program.statement.SLListOfIStatement;
import de.uka.ilkd.key.lang.clang.common.programmeta.IClangProgramMeta;
import de.uka.ilkd.key.lang.clang.common.programsv.TypeProgramSV;
import de.uka.ilkd.key.lang.clang.common.programsv.VariableProgramSV;
import de.uka.ilkd.key.lang.clang.common.sort.IClangObjectSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IInstantiableObjectSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IStructuredSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.MemberInfo;
import de.uka.ilkd.key.lang.clang.common.type.IClangInstantiableObjectType;
import de.uka.ilkd.key.lang.clang.common.type.IClangObjectType;
import de.uka.ilkd.key.lang.clang.common.type.declaration.MemberDecl;
import de.uka.ilkd.key.lang.clang.common.type.declaration.StructDecl;
import de.uka.ilkd.key.lang.clang.common.type.declaration.StructuredTypeDecl;
import de.uka.ilkd.key.lang.clang.common.type.object.ArrayType;
import de.uka.ilkd.key.lang.clang.common.type.object.ScalarType;
import de.uka.ilkd.key.lang.clang.common.type.object.StructType;
import de.uka.ilkd.key.lang.clang.common.type.value.PointerType;
import de.uka.ilkd.key.lang.clang.common.util.TypePairUtil;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.program.IVariable;
import de.uka.ilkd.key.lang.common.programsv.ArrayOfBaseProgramSV;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.ProgramSV;

/**
 * A loader of C programs. Allows loading normalized programs
 * and legal sequences of C statements.
 * 
 * @author oleg.myrk@gmail.com
 */
public class Loader {
        private final ILoaderConfiguration configuration;
        private final IClangEnvironment environment;
        private final IClangPlatform platform;
        
        private final Namespace schemaVariableNS;
        private final Namespace programVariableNS;

        /**
         * Records current loading context, useful for error reporting.
         */
        private LoadingContext currentContext;

        /**
         * A namespace of variables accessible in the current block. All
         * variables have unique names. The element type is
         * {@link IVariable}.
         */
        private Namespace blockVariableNS;

        /**
         * A namespace of variables accessible in the current block indexed by
         * their real name (before renaming). The element type is
         * {@link RenamedVariable}.
         */
        private Namespace blockRenamedVariableNS;

        private Loader(ILoaderConfiguration configuration, Namespace schemaVariableNS,
                        Namespace programVariableNS) {
                this.configuration = configuration;
                this.environment = configuration.getEnvironment();
                this.platform = environment.getPlatform();
                this.schemaVariableNS = schemaVariableNS;
                this.programVariableNS = programVariableNS;

                this.initBlockProtocol();
        }

        /**
         * Sets the current conversion context, useful for error reporting.
         * @param conversionContext
         */
        private void setConversionContext(LoadingContext conversionContext) {
                this.currentContext = conversionContext;
        }

        /**
         * Loads a normalized program.
         * 
         * @param configuration
         * @param files
         * @throws IOException
         * @throws ConversionException
         */
        public static void loadProgram(ILoaderConfiguration configuration, String[] files)
                        throws IOException, ConversionException {
                // Reset strategy
                ParserStrategy.getInstance().reset(new Namespace());

                Loader instance = new Loader(configuration, null, null);
                for (int i = 0; i < files.length; i++) {
                        TranslationUnit translationUnit;
                        try {
                                CLexer lexer = new CLexer(new BufferedInputStream(new FileInputStream(files[i])));
                                lexer.setOriginalSource(files[i]);
                                lexer.setTokenObjectClass("de.uka.ilkd.key.lang.clang.common.loader.parser.CToken");
                                lexer.initialize();

                                CParser parser = new CParser(lexer);
                                parser.getPreprocessorInfoChannel(lexer.getPreprocessorInfoChannel());
                                parser.setLexer(lexer);

                                translationUnit = new cetus.hir.TranslationUnit(files[i]);
                                parser.translationUnit(translationUnit);
                                Class[] params = new Class[2];
                                params[0] = TranslationUnit.class;
                                params[1] = OutputStream.class;
                                try {
                                        translationUnit.setPrintMethod(params[0].getMethod("defaultPrint2", params));
                                } catch (Exception e) {
                                        throw new RuntimeException(e);
                                }
                        } catch (RuntimeException e) {
                                if (e.getCause() != null
                                                && e.getCause() instanceof antlr.RecognitionException) {
                                        antlr.RecognitionException c = (antlr.RecognitionException) e
                                                        .getCause();
                                        throw new ConversionException(
                                                        c.getMessage(),
                                                        new LoadingContext(
                                                                        files[i],
                                                                        new int[] {
                                                                                        c
                                                                                                        .getLine(),
                                                                                        c
                                                                                                        .getColumn() },
                                                                        null),
                                                        c);
                                } else
                                        throw e;
                        } catch (antlr.ANTLRException e) {
                                throw new RuntimeException(e);
                        }

                        // Convert
                        instance.setConversionContext(new LoadingContext(
                                        files[i], (String) null, null));
                        instance
                                        .loadTranslationUnit(translationUnit);

                }
        }

        /**
         * Loads a legal sequence of statements.
         * 
         * @param configuration
         * @param schemaVariableNS
         * @param programVariableNS
         * @param code
         * @return
         * @throws ConversionException
         */
        public static IProgramElement loadProgramStatements(ILoaderConfiguration configuration,
                        Namespace schemaVariableNS,
                        Namespace programVariableNS, String code)
                        throws ConversionException {
                // Create input stream
                DataInputStream inputStream;
                try {
                        ByteArrayOutputStream byteStream = new ByteArrayOutputStream();
                        OutputStreamWriter writer = new OutputStreamWriter(
                                        byteStream);
                        writer.write(code);
                        writer.flush();
                        inputStream = new DataInputStream(
                                        new ByteArrayInputStream(byteStream
                                                        .toByteArray()));
                } catch (IOException e) {
                        throw new RuntimeException(e);
                }

                // Create lexer
                SchemaCLexer lexer = new SchemaCLexer(inputStream);
                lexer.setOriginalSource(code);
                lexer.setTokenObjectClass("de.uka.ilkd.key.lang.clang.common.loader.parser.CToken");
                lexer.initialize();

                // Create parser
                SchemaCParser parser = new SchemaCParser(lexer);
                parser
                                .getPreprocessorInfoChannel(new PreprocessorInfoChannel());
                parser.setLexer(lexer);

                // Run the parser
                cetus.hir.CompoundStatement compoundStatement = null;
                try {
                        // Reset strategy
                        ParserStrategy.getInstance().reset(schemaVariableNS);
                        compoundStatement = parser.codeBlock();

                } catch (RuntimeException e) {
                        if (e.getCause() != null
                                        && e.getCause() instanceof antlr.RecognitionException) {
                                antlr.RecognitionException c = (antlr.RecognitionException) e
                                                .getCause();
                                throw new ConversionException(
                                                c.getMessage(),
                                                new LoadingContext(
                                                                c.getFilename(),
                                                                new int[] {
                                                                                c
                                                                                                .getLine(),
                                                                                c
                                                                                                .getColumn() },
                                                                code), c);
                        } else
                                throw e;
                } catch (antlr.ANTLRException e) {
                        throw new RuntimeException(e);
                }

                // Do the conversion
                Loader instance = new Loader(configuration,
                                schemaVariableNS, programVariableNS);
                instance.setConversionContext(new LoadingContext(null,
                                (String) null, code));
                return instance.convertCompoundStatement(compoundStatement);
        }

        private void loadTranslationUnit(
                        cetus.hir.TranslationUnit translationUnit)
                        throws ConversionException {
                List children = translationUnit.getChildren();

                for (Iterator i = children.iterator(); i.hasNext();) {
                        Object child = i.next();
                        // Process struct and union declarations
                        if (child instanceof cetus.hir.ClassDeclaration)
                                loadClassDeclaration((cetus.hir.ClassDeclaration) child);
                }
        }

        private void loadClassDeclaration(
                        cetus.hir.ClassDeclaration classDeclaration)
                        throws ConversionException {
                cetus.hir.Identifier name = (cetus.hir.Identifier) readHiddenField(
                                classDeclaration, "name");

                Object key = readHiddenField(classDeclaration, "type");

                if (key == cetus.hir.ClassDeclaration.STRUCT) {
                        String id = name.getName();
                        
                        // Lookup up struct decl
                        StructDecl structDecl = configuration.getTypeBuilder().getStructDecl(id);
                        
                        // If struct has not been declared yet
                        if (structDecl == null) {
                                structDecl = new StructDecl(id);
                                configuration.getTypeBuilder().addStructDecl(structDecl);
                        }
                        
                        // Lookup struct sort
                        ILoaderConfiguration.StructSortInfo structSortInfo = configuration.getStructSortInfo(id);
                        
                        // If this declaration also declares members
                        if (classDeclaration.getChildren() != null) {
                                if (structDecl.getMembersDefined())
                                        throw buildConvertException(
                                                        "Duplicate struct members declaration",
                                                        classDeclaration);
                                assert !structSortInfo.wasRegistered();
                                
                                // Add member declarations
                                for (Iterator i = classDeclaration
                                                .getChildren().iterator(); i
                                                .hasNext();) {
                                        cetus.hir.Declaration declaration = ((cetus.hir.DeclarationStatement) i
                                                        .next())
                                                        .getDeclaration();

                                        if (declaration instanceof cetus.hir.VariableDeclaration) {
                                                cetus.hir.VariableDeclaration variableDeclaration = (cetus.hir.VariableDeclaration) declaration;
                                                List specifiers = variableDeclaration
                                                                .getSpecifiers();

                                                // Convert the type specifiers
                                                KeYJavaType specifierType = computeTypeFromSpecifiers(
                                                                specifiers,
                                                                variableDeclaration);

                                                // Process declarators
                                                int numDeclarators = variableDeclaration
                                                                .getNumDeclarators();

                                                for (int j = 0; j < numDeclarators; j++) {
                                                        cetus.hir.Declarator declarator = variableDeclaration
                                                                        .getDeclarator(j);

                                                        if (declarator
                                                                        .getInitializer() != null)
                                                                throw buildConvertException(
                                                                                "Member declaration initializers are not supported",
                                                                                declarator);

                                                        KeYJavaType type = computeTypeFromDeclarator(
                                                                        declarator,
                                                                        specifierType);

                                                        if (!(type
                                                                        .getJavaType() instanceof IClangInstantiableObjectType))
                                                                throw buildConvertException(
                                                                                "Member type should be instantiable object type",
                                                                                declarator);
                                                        assert type.getSort() instanceof IInstantiableObjectSort;

                                                        // Process the symbol
                                                        if (!(declarator
                                                                        .getSymbol() instanceof cetus.hir.Identifier))
                                                                throw buildConvertException(
                                                                                "Schema variables cannot be used in member declarations",
                                                                                declarator);

                                                        cetus.hir.Identifier symbol = (cetus.hir.Identifier) declarator
                                                                        .getSymbol();

                                                        // Add struct member (Type)
                                                        structDecl
                                                                        .getMemberMap()
                                                                        .put(
                                                                                        symbol
                                                                                                        .getName(),
                                                                                        new MemberDecl(
                                                                                                        symbol
                                                                                                                        .getName(),
                                                                                                        (IClangInstantiableObjectType) type
                                                                                                                        .getJavaType(),
                                                                                                        j));

                                                        
                                                        // Add struct member (Sort)
                                                        structSortInfo.addMember(new MemberInfo(symbol.getName(), (IInstantiableObjectSort)type.getSort(), j));
                                                        
                                                }
                                        }

                                }

                                // Mark sort declaration members defiend
                                structDecl.setMembersDefined();
                                
                                // Register the struct sort
                                structSortInfo.register();
                        }
                        // If members are not declared here
                        else {
                                // If the members are never declared, the srtuct
                                // sort remains unregistered in the namespaces
                        }
                }
        }

        private IClangStatement convertCompoundStatement(
                        cetus.hir.CompoundStatement compoundStatement)
                        throws ConversionException {
                enterBlock();
                try {
                        List statements = compoundStatement.getChildren();

                        ListOfIStatement children = SLListOfIStatement.EMPTY_LIST;
                        for (Iterator i = statements.iterator(); i.hasNext();) {
                                cetus.hir.Statement statement = (cetus.hir.Statement) i
                                                .next();
                                children = children
                                                .append(convertStatement(statement));
                        }

                        if (compoundStatement instanceof de.uka.ilkd.key.lang.clang.common.loader.util.RootFrame) {
                                return new de.uka.ilkd.key.lang.clang.common.program.statement.RootFrame(
                                                new de.uka.ilkd.key.lang.clang.common.program.statement.FrameBody(
                                                                new ArrayOfIClangStatement(
                                                                                children
                                                                                                .toArray())));
                        } else if (compoundStatement instanceof de.uka.ilkd.key.lang.clang.common.loader.util.ContextFrame) {
                                return new de.uka.ilkd.key.lang.clang.common.program.statement.ContextFrame(
                                                new ArrayOfIClangStatement(children
                                                                .toArray()));
                        } else {
                                return new de.uka.ilkd.key.lang.clang.common.program.statement.CompoundStatement(
                                                new ArrayOfIClangStatement(children
                                                                .toArray()));
                        }
                } finally {
                        leaveBlock();
                }
        }

        public IClangStatement convertSingleStatement(cetus.hir.Statement statement)
                        throws ConversionException {
                ListOfIStatement list = convertStatement(statement);

                if (list.size() == 1)
                        return list.head();
                else
                        return new de.uka.ilkd.key.lang.clang.common.program.statement.CompoundStatement(
                                        new ArrayOfIClangStatement(list.toArray()));
        }

        public ListOfIStatement convertStatement(cetus.hir.Statement statement)
                        throws ConversionException {
                ListOfIStatement list = SLListOfIStatement.EMPTY_LIST;

                if (statement instanceof StatementSVWrapper) {
                        return list.append(((StatementSVWrapper) statement)
                                        .getSV());
                }

                if (statement instanceof cetus.hir.CompoundStatement) {
                        return list
                                        .append(convertCompoundStatement((cetus.hir.CompoundStatement) statement));

                }

                if (statement instanceof cetus.hir.DeclarationStatement) {
                        return list
                                        .append(convertDeclarationStatement((cetus.hir.DeclarationStatement) statement));

                }

                if (statement instanceof cetus.hir.IfStatement) {
                        cetus.hir.IfStatement ifStatement = (cetus.hir.IfStatement) statement;
                        IClangExpression convertedControlExpression = convertExpression(ifStatement
                                        .getControlExpression());
                        de.uka.ilkd.key.lang.clang.common.program.statement.Branch convertedThenBranch = new de.uka.ilkd.key.lang.clang.common.program.statement.Branch(
                                        convertSingleStatement(ifStatement
                                                        .getThenStatement()));
                        de.uka.ilkd.key.lang.clang.common.program.statement.Branch convertedElseBranch = ifStatement
                                        .getElseStatement() != null ? new de.uka.ilkd.key.lang.clang.common.program.statement.Branch(
                                        convertSingleStatement(ifStatement
                                                        .getElseStatement()))
                                        : null;
                        return list
                                        .append(new de.uka.ilkd.key.lang.clang.common.program.statement.IfStatement(
                                                        ensureValueExpression(convertedControlExpression),
                                                        convertedThenBranch,
                                                        convertedElseBranch));
                }

                if (statement instanceof cetus.hir.WhileLoop) {
                        cetus.hir.WhileLoop whileLoop = (cetus.hir.WhileLoop) statement;
                        IClangExpression convertedControlExpression = convertExpression(whileLoop
                                        .getCondition());
                        de.uka.ilkd.key.lang.clang.common.program.statement.Branch convertedBody = new de.uka.ilkd.key.lang.clang.common.program.statement.Branch(
                                        convertSingleStatement(whileLoop
                                                        .getBody()));
                        return list
                                        .append(new de.uka.ilkd.key.lang.clang.common.program.statement.WhileStatement(
                                                        ensureValueExpression(convertedControlExpression),
                                                        convertedBody));
                }

                if (statement instanceof cetus.hir.ExpressionStatement) {
                        cetus.hir.ExpressionStatement expressionStatement = (cetus.hir.ExpressionStatement) statement;
                        IClangExpression expressionConverted = convertExpression(expressionStatement
                                        .getExpression());
                        return list
                                        .append(new de.uka.ilkd.key.lang.clang.common.program.statement.ExpressionStatement(
                                                        expressionConverted));
                }

                if (statement instanceof de.uka.ilkd.key.lang.clang.common.loader.util.AllocateStatement) {
                        de.uka.ilkd.key.lang.clang.common.loader.util.AllocateStatement allocateStatement = (de.uka.ilkd.key.lang.clang.common.loader.util.AllocateStatement) statement;
                        IClangExpression expressionConverted = convertExpression(allocateStatement
                                        .getExpression());
                        return list
                                        .append(new de.uka.ilkd.key.lang.clang.common.program.statement.AllocateStatement(
                                                        expressionConverted));
                }

                if (statement instanceof de.uka.ilkd.key.lang.clang.common.loader.util.DestroyStatement) {
                        de.uka.ilkd.key.lang.clang.common.loader.util.DestroyStatement destroyStatement = (de.uka.ilkd.key.lang.clang.common.loader.util.DestroyStatement) statement;
                        IClangExpression expressionConverted = convertExpression(destroyStatement
                                        .getExpression());
                        return list
                                        .append(new de.uka.ilkd.key.lang.clang.common.program.statement.DestroyStatement(
                                                        expressionConverted));
                }

                if (statement instanceof de.uka.ilkd.key.lang.clang.common.loader.util.MetaStatement) {
                        de.uka.ilkd.key.lang.clang.common.loader.util.MetaStatement metaStatement = (de.uka.ilkd.key.lang.clang.common.loader.util.MetaStatement) statement;
                        ArrayOfBaseProgramSV arguments = new ArrayOfBaseProgramSV(
                                        metaStatement.getArguments());
                        
                        IClangProgramMeta metaConstruct = configuration
                                        .getProgramMetaConstruct(
                                                        new Name(
                                                                        metaStatement
                                                                                        .getName()), arguments);

                        if (metaConstruct == null)
                                throw buildConvertException(
                                                "Program meta construct does not exist",
                                                statement);

                        if (!(metaConstruct instanceof IClangStatement))
                                throw buildConvertException(
                                                "Program meta construct '"
                                                                + metaStatement
                                                                                .getName()
                                                                + "' cannot be used as a statement",
                                                statement);
                        return list.append((IClangStatement) metaConstruct);
                }

                /*
                 * if (statement instanceof cetus.hir.WhileLoop) return
                 * convertWhileLoop((cetus.hir.WhileLoop)statement);
                 * 
                 * if (statement instanceof cetus.hir.IfStatement) return
                 * convertIfStatement((cetus.hir.IfStatement)statement);
                 * 
                 * if (statement instanceof cetus.hir.NullStatement) return
                 * convertNullStatement((cetus.hir.NullStatement)statement);
                 */
                throw buildConvertException("No supported statement", statement);
        }

        private ListOfIStatement convertDeclarationStatement(
                        cetus.hir.DeclarationStatement declarationStatement)
                        throws ConversionException {
                ListOfIStatement list = SLListOfIStatement.EMPTY_LIST;

                cetus.hir.Declaration declaration = declarationStatement
                                .getDeclaration();

                if (declaration instanceof cetus.hir.VariableDeclaration) {
                        cetus.hir.VariableDeclaration variableDeclaration = (cetus.hir.VariableDeclaration) declaration;
                        List specifiers = variableDeclaration.getSpecifiers();

                        // Process specifiers
                        boolean isStatic = false;
                        boolean isRegister = false;
                        TypeSVWrapper schemaTypeSpecifier = null;
                        List newSpecifiers = new LinkedList();
                        for (int j = 0; j < specifiers.size(); j++) {
                                cetus.hir.Specifier specifier = (cetus.hir.Specifier) specifiers
                                                .get(j);

                                if (specifier == cetus.hir.Specifier.STATIC)
                                        isStatic = true;
                                else if (specifier == cetus.hir.Specifier.REGISTER)
                                        isRegister = true;
                                else if (specifier instanceof TypeSVWrapper)
                                        schemaTypeSpecifier = (TypeSVWrapper) specifier;
                                else
                                        newSpecifiers.add(specifier);
                        }

                        // If schema delaration
                        if (schemaTypeSpecifier != null) {
                                if (!newSpecifiers.isEmpty() || isRegister)
                                        throw buildConvertException(
                                                        "Wrong schema variable declaration",
                                                        declaration);

                                return list
                                                .append(convertSchemaTypeVariableDeclaration(
                                                                variableDeclaration,
                                                                schemaTypeSpecifier,
                                                                isStatic));
                        }
                        // If normal declaration
                        else {
                                // Convert the type specifiers
                                KeYJavaType specifierType = computeTypeFromSpecifiers(
                                                newSpecifiers,
                                                variableDeclaration);

                                // Process declarators
                                int numDeclarators = variableDeclaration
                                                .getNumDeclarators();

                                // If one declarator
                                if (numDeclarators == 1) {
                                        return list
                                                        .append(convertVariableDeclarator(
                                                                        variableDeclaration
                                                                                        .getDeclarator(0),
                                                                        specifierType,
                                                                        isStatic,
                                                                        isRegister));
                                }
                                // If multiple declarators
                                else {
                                        // Create a new compound statement of
                                        // declarations
                                        for (int i = 0; i < numDeclarators; i++)
                                                list = list
                                                                .append(convertVariableDeclarator(
                                                                                variableDeclaration
                                                                                                .getDeclarator(i),
                                                                                specifierType,
                                                                                isStatic,
                                                                                isRegister));

                                        return list;
                                }
                        }
                }

                throw buildConvertException("Unsupported declaration format",
                                declaration);
        }

        private IClangStatement convertSchemaTypeVariableDeclaration(
                        cetus.hir.VariableDeclaration declaration,
                        TypeSVWrapper schemaTypeSpecifier, boolean isStatic)
                        throws ConversionException {
                // Process schema type specifier
                TypeProgramSV typeReference = ((TypeSVWrapper) schemaTypeSpecifier)
                                .getSV();

                // Process the schema declarator
                if (declaration.getNumDeclarators() != 1)
                        throw buildConvertException(
                                        "Wrong schema variable declaration",
                                        declaration);

                cetus.hir.Declarator declarator = declaration.getDeclarator(0);

                // Check that declarator consists only of a schema program
                // variable
                if (declarator.getArraySpecifiers() != null
                                || declarator.getPointerSpecifiers() != null
                                || declarator.getParameters() != null
                                || !(declarator.getSymbol() instanceof VariableSVWrapper))
                        throw buildConvertException(
                                        "Wrong schema variable declaration",
                                        declaration);

                VariableSVWrapper variableSVWrapper = (VariableSVWrapper) declarator
                                .getSymbol();
                VariableProgramSV variable = (variableSVWrapper.getSV());

                // Initializer expression
                IClangExpression convertedInitializer = null;
                if (declarator.getInitializer() != null) {
                        cetus.hir.Initializer initializer = declarator
                                        .getInitializer();
                        convertedInitializer = convertInitializer(initializer);

                        if (!(convertedInitializer != null & convertedInitializer instanceof ProgramSV))
                                throw buildConvertException(
                                                "Schema variable declarations can have only schema initializers",
                                                initializer);
                }

                // Build variable declaration
                return new de.uka.ilkd.key.lang.clang.common.program.declaration.VariableDeclaration(
                                typeReference,
                                variable,
                                convertedInitializer,
                                isStatic
                                );
        }

        private IClangStatement convertVariableDeclarator(
                        cetus.hir.Declarator declarator,
                        KeYJavaType specifierType, boolean isStatic,
                        boolean isRegister) throws ConversionException {
                KeYJavaType type = computeTypeFromDeclarator(declarator,
                                specifierType);
                if (isRegister && type.getJavaType() instanceof ScalarType) {
                        type = TypePairUtil.extractFromScalarType(type);
                } else {
                        if (!(type.getJavaType() instanceof IClangInstantiableObjectType))
                                throw buildConvertException(
                                                "Variable type should be instantiable object type",
                                                declarator);
                        assert type.getSort() instanceof IInstantiableObjectSort;
                }

                de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference typeReference = new de.uka.ilkd.key.lang.clang.common.program.type.TypeReference(
                                type);

                // Process the symbol
                de.uka.ilkd.key.lang.clang.common.program.iface.IClangVariable programVariable;
                if (declarator.getSymbol() instanceof cetus.hir.Identifier) {
                        cetus.hir.Identifier symbol = (cetus.hir.Identifier) declarator
                                        .getSymbol();
                        Name realName = buildVariableName(symbol
                                        .getName());
                        Name name = realName;

                        // Check for name clashes
                        if (isBlockVariableDuplicate(realName))
                                throw buildConvertException(
                                                "Variable declared multiple times",
                                                declarator);
                        if (isBlockVariableClashing(realName))
                                name = buildBlockUniqueVariableName(name);

                        // Register the new variable
                        programVariable = new de.uka.ilkd.key.lang.clang.common.program.variable.Variable(
                                        name, type);
                        registerBlockVariable(realName, programVariable);
                } else if (declarator.getSymbol() instanceof VariableSVWrapper) {
                        VariableSVWrapper variableSVWrapper = (VariableSVWrapper) declarator
                                        .getSymbol();
                        programVariable = (variableSVWrapper.getSV());
                } else
                        throw buildConvertException(
                                        "Wrong variable declarator:",
                                        declarator);

                // Initializer expression
                IClangExpression convertedInitializer = null;
                if (declarator.getInitializer() != null) {
                        cetus.hir.Initializer initializer = declarator
                                        .getInitializer();
                        convertedInitializer = convertInitializer(initializer);

                        if (convertedInitializer == null)
                                throw buildConvertException(
                                                "Unsupported intializer format",
                                                declarator);

                        // Type check
                        try {
                                new de.uka.ilkd.key.lang.clang.common.program.expression.operator.ValueAssignment(
                                                ensureValueExpression((IClangExpression) programVariable),
                                                convertedInitializer)
                                                .getTypePair(configuration.getEnvironment());
                        } catch (TypeErrorException e) {
                                throw buildConvertException(e
                                                .getLocalizedMessage(),
                                                initializer);
                        }
                }

                // Build variable declaration
                return new de.uka.ilkd.key.lang.clang.common.program.declaration.VariableDeclaration(
                                typeReference,
                                programVariable, 
                                convertedInitializer,
                                isStatic);

        }

        private KeYJavaType computeTypeFromSpecifiers(List specifiers,
                        cetus.hir.Printable parent) throws ConversionException {
                boolean hadSigned = false;
                boolean hadUnsigned = false;
                boolean hadChar = false;
                boolean hadShort = false;
                boolean hadInt = false;
                boolean hadVoid = false;
                int countLong = 0;

                KeYJavaType structTypePair = null;

                for (int i = 0; i < specifiers.size(); i++) {
                        boolean recognized = false;
                        cetus.hir.Specifier specifier = (cetus.hir.Specifier) specifiers
                                        .get(i);

                        if (specifier == cetus.hir.Specifier.SIGNED) {
                                hadSigned = true;
                                recognized = true;
                        } else if (specifier == cetus.hir.Specifier.UNSIGNED) {
                                hadUnsigned = true;
                                recognized = true;
                        } else if (specifier == cetus.hir.Specifier.CHAR) {
                                hadChar = true;
                                recognized = true;
                        } else if (specifier == cetus.hir.Specifier.SHORT) {
                                hadShort = true;
                                recognized = true;
                        } else if (specifier == cetus.hir.Specifier.INT) {
                                hadInt = true;
                                recognized = true;
                        } else if (specifier == cetus.hir.Specifier.LONG) {
                                countLong++;
                                recognized = true;
                        } else if (specifier == cetus.hir.Specifier.VOID) {
                                hadVoid = true;
                                recognized = true;
                        } else if (specifier instanceof cetus.hir.UserSpecifier) {
                                cetus.hir.UserSpecifier userSpecifier = (cetus.hir.UserSpecifier) specifier;
                                cetus.hir.IDExpression idExpression = (cetus.hir.IDExpression) readHiddenField(
                                                userSpecifier, "usertype");
                                if (idExpression instanceof cetus.hir.Identifier) {
                                        cetus.hir.Identifier id = (cetus.hir.Identifier) idExpression;
                                        if (id.getName().startsWith("struct ")) {
                                                String structId = id
                                                                .getName()
                                                                .substring(
                                                                                "struct "
                                                                                                .length());
                                                structTypePair = platform.getStructTypePair(structId);
                                                if (structTypePair == null)
                                                        throw buildConvertException(
                                                                        "Unknown struct",
                                                                        specifier);
                                                recognized = true;
                                        }
                                }
                        }

                        if (!recognized)
                                throw buildConvertException(
                                                "Unsupported type specifier",
                                                specifier);

                }

                // TODO: detect error cases
                // @author oleg.myrk@gmail.com

                // char
                if (hadChar && !hadSigned && !hadUnsigned)
                        return platform.getScalarTypePair(platform.getIntegerTypePair(platform.getCHARId()));

                // signed char
                if (hadChar && hadSigned)
                        return platform.getScalarTypePair(platform.getIntegerTypePair(platform.getSCHARId()));

                // unsigned char
                if (hadChar && hadUnsigned)
                        return platform.getScalarTypePair(platform.getIntegerTypePair(platform.getUCHARId()));

                // signed short
                if (hadShort && !hadUnsigned)
                        return platform.getScalarTypePair(platform.getIntegerTypePair(platform.getSSHRTId()));

                // unsigned short
                if (hadShort && hadUnsigned)
                        return platform.getScalarTypePair(platform.getIntegerTypePair(platform.getUSHRTId()));

                // signed int
                if (hadInt && !hadUnsigned)
                        return platform.getScalarTypePair(platform.getIntegerTypePair(platform.getSINTId()));

                // unsigned int
                if (hadInt && hadUnsigned)
                        return platform.getScalarTypePair(platform.getIntegerTypePair(platform.getUINTId()));

                // signed long
                if (countLong == 1 && !hadUnsigned)
                        return platform.getScalarTypePair(platform.getIntegerTypePair(platform.getSLONGId()));

                // unsigned long
                if (countLong == 1 && hadUnsigned)
                        return platform.getScalarTypePair(platform.getIntegerTypePair(platform.getULONGId()));

                // signed long long
                if (countLong == 2 && !hadUnsigned)
                        return platform.getScalarTypePair(platform.getIntegerTypePair(platform.getSLLONGId()));

                // unsigned long long
                if (countLong == 2 && hadUnsigned)
                        return platform.getScalarTypePair(platform.getIntegerTypePair(platform.getULLONGId()));

                // void
                if (hadVoid)
                        return platform.getVoidTypePair();

                // struct Id
                if (structTypePair != null)
                        return structTypePair;

                throw buildConvertException("Unsuported type specifier format",
                                parent);
        }

        private KeYJavaType computeTypeFromDeclarator(
                        cetus.hir.Declarator declarator, KeYJavaType type)
                        throws ConversionException {

                // Test for function pointers
                if (declarator.getParameters() != null)
                        throw buildConvertException(
                                        "Function pointers not supported",
                                        declarator);

                // Work with array declarators
                if (declarator.getArraySpecifiers() != null) {
                        if (!(type.getJavaType() instanceof IClangInstantiableObjectType))
                                throw buildConvertException(
                                                "Array declarator applied should be applied to instantiable object type",
                                                declarator);
                        assert type.getSort() instanceof IInstantiableObjectSort;

                        List arraySpecifiers = declarator.getArraySpecifiers();
                        for (int i = 0; i < arraySpecifiers.size(); i++) {
                                cetus.hir.ArraySpecifier arraySpecifier = (cetus.hir.ArraySpecifier) arraySpecifiers
                                                .get(i);
                                if (arraySpecifier == cetus.hir.ArraySpecifier.UNBOUNDED)
                                        throw buildConvertException(
                                                        "Unbounded arrays in declarators not supported",
                                                        declarator);
                                for (int j = 0; j < arraySpecifier
                                                .getNumDimensions(); j++) {
                                        cetus.hir.Expression dimension = arraySpecifier
                                                        .getDimension(j);

                                        if (!(dimension instanceof cetus.hir.IntegerLiteral))
                                                throw buildConvertException(
                                                                "Constant expressions not supported in declarators",
                                                                declarator);

                                        BigInteger size = BigInteger
                                                        .valueOf(((cetus.hir.IntegerLiteral) dimension)
                                                                        .getValue());

                                        type = platform.getArrayTypePair(type, size);
                                }

                        }

                }

                // Work with pointer declarators
                if (declarator.getPointerSpecifiers() != null) {
                        if (!(type.getJavaType() instanceof IClangObjectType))
                                throw buildConvertException(
                                                "Pointer declarator should be applied to object type",
                                                declarator);
                        assert type.getSort() instanceof IClangObjectSort;

                        int pointerCount = declarator.getPointerSpecifiers()
                                        .size();
                        for (int i = 0; i < pointerCount; i++)
                                type = platform.getScalarTypePair(platform.getPointerTypePair(type));
                }

                // Worke with nested declarator
                cetus.hir.Declarator nestedDeclarator = (cetus.hir.Declarator) readHiddenField(
                                declarator, "nested_decl");
                if (nestedDeclarator != null)
                        type = computeTypeFromDeclarator(nestedDeclarator, type);

                // Complete
                return type;
        }

        private IClangExpression convertInitializer(cetus.hir.Initializer initializer)
                        throws ConversionException {
                cetus.hir.Expression value = (cetus.hir.Expression) readHiddenField(
                                initializer, "value");
                if (value != null)
                        return ensureValueExpression(convertExpression(value));
                else
                        return null;
        }

        private IClangExpression convertExpression(cetus.hir.Expression expression)
                        throws ConversionException {
                return convertExpression(expression, null);
        }

        private IClangExpression convertExpression(cetus.hir.Expression expression,
                        KeYJavaType castTypePair) throws ConversionException {
                IClangExpression convertedExpression = convertExpressionRaw(
                                expression, castTypePair);
                try {
                        getExpressionType(convertedExpression);
                        return convertedExpression;
                } catch (TypeErrorException e) {
                        throw buildConvertException(e.getLocalizedMessage(),
                                        expression);
                }
        }

        private IClangExpression convertExpressionRaw(
                        cetus.hir.Expression expression,
                        KeYJavaType castTypePair) throws ConversionException {
                if (expression instanceof ExpressionSVWrapper) {
                        ExpressionSVWrapper expressionSVWrapper = (ExpressionSVWrapper) expression;
                        // Schema expression
                        return (expressionSVWrapper.getSV());
                } else if (expression instanceof cetus.hir.Identifier) {
                        cetus.hir.Identifier identifier = (cetus.hir.Identifier) expression;

                        // Getting program variable from namespace
                        BaseClangVariable programVariable = (BaseClangVariable) lookupVariable(new Name(
                                        identifier.getName()));

                        if (programVariable == null)
                                throw buildConvertException(
                                                "Variable is not declared",
                                                expression);

                        return programVariable;
                } else if (expression instanceof cetus.hir.IntegerLiteral) {
                        cetus.hir.IntegerLiteral integerLiteral = (cetus.hir.IntegerLiteral) expression;
                        return new de.uka.ilkd.key.lang.clang.common.program.expression.literal.IntegerLiteral(
                                        BigInteger.valueOf(integerLiteral
                                                        .getValue()),
                                        platform.getIntegerTypePair(platform.getSINTId()));
                } else if (expression instanceof cetus.hir.UnaryExpression
                                && ((cetus.hir.UnaryExpression) expression)
                                                .getOperator() == de.uka.ilkd.key.lang.clang.common.loader.util.ValueOfOperator.VALUE_OF) {
                        cetus.hir.UnaryExpression unaryExpression = (cetus.hir.UnaryExpression) expression;
                        cetus.hir.Expression subExpression = unaryExpression
                                        .getExpression();
                        IClangExpression subExpressionConverted = convertExpression(subExpression);

                        return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.ValueOf(
                                        subExpressionConverted);
                } else if (expression instanceof cetus.hir.UnaryExpression
                                && ((cetus.hir.UnaryExpression) expression)
                                                .getOperator() == de.uka.ilkd.key.lang.clang.common.loader.util.ParenthesesOperator.PARENTHESES) {
                        cetus.hir.UnaryExpression unaryExpression = (cetus.hir.UnaryExpression) expression;
                        cetus.hir.Expression subExpression = unaryExpression
                                        .getExpression();
                        IClangExpression subExpressionConverted = convertExpression(subExpression);

                        return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.Parentheses(
                                        subExpressionConverted);
                } else if (expression instanceof cetus.hir.AccessExpression
                                && (((cetus.hir.AccessExpression) expression)
                                                .getOperator() == cetus.hir.AccessOperator.MEMBER_ACCESS || ((cetus.hir.AccessExpression) expression)
                                                .getOperator() == cetus.hir.AccessOperator.POINTER_ACCESS)) {
                        cetus.hir.AccessExpression accessExpression = (cetus.hir.AccessExpression) expression;
                        cetus.hir.AccessOperator accessOperator = (cetus.hir.AccessOperator) accessExpression
                                        .getOperator();
                        cetus.hir.Expression subExpression = accessExpression
                                        .getLHS();
                        cetus.hir.Expression memberExpression = accessExpression
                                        .getRHS();
                        IClangExpression subExpressionConverted = convertExpression(subExpression);

                        // If concrete member accessor
                        if (memberExpression instanceof cetus.hir.Identifier) {
                                String memberName = ((cetus.hir.Identifier) memberExpression)
                                                .getName();

                                // Compute sub expression type
                                KeYJavaType subExpressionType;
                                subExpressionType = getExpressionType(subExpressionConverted);
                                if (subExpressionType == null)
                                        throw buildConvertException(
                                                        "Concrete member accessor applied to schema expression",
                                                        expression);

                                // Compute target type
                                KeYJavaType targetType = null;
                                if (accessOperator == cetus.hir.AccessOperator.MEMBER_ACCESS)
                                        targetType = subExpressionType;
                                else {
                                        if (!(subExpressionType.getJavaType() instanceof PointerType))
                                                throw buildConvertException(
                                                                "Member pointer accessor applied to non-pointer type \""
                                                                                + subExpressionType
                                                                                                .getJavaType()
                                                                                                .getName()
                                                                                + "\"",
                                                                expression);
                                        targetType = TypePairUtil.extractFromPointerType(subExpressionType);
                                }

                                // Make sure target type is a structured type
                                if (!(targetType.getJavaType() instanceof StructType))
                                        throw buildConvertException(
                                                        "Member accessor applied to non-struct type \""
                                                                        + targetType
                                                                                        .getJavaType()
                                                                                        .getName()
                                                                        + "\"",
                                                        expression);
                                assert targetType.getSort() instanceof IStructuredSort;

                                StructuredTypeDecl structuredDecl = ((StructType) targetType
                                                .getJavaType()).getDecl();
                                IStructuredSort structuredSort = (IStructuredSort) targetType
                                                .getSort();

                                // Find the member
                                MemberDecl memberDecl = structuredDecl
                                                .getMemberMap().get(memberName);
                                MemberInfo memberInfo = structuredSort
                                                .getMemberInfoMap().get(
                                                                memberName);
                                if (memberDecl == null)
                                        throw buildConvertException(
                                                        "Accessing non-existent member of type \""
                                                                        + targetType
                                                                                        .getJavaType()
                                                                        + "\"",
                                                        expression);
                                assert memberInfo != null;

                                // Build member accessor
                                de.uka.ilkd.key.lang.clang.common.program.expression.operator.MemberReference memberReference = new de.uka.ilkd.key.lang.clang.common.program.expression.operator.MemberReference(
                                                new Name(memberName),
                                                new KeYJavaType(
                                                                memberDecl
                                                                                .getType(),
                                                                memberInfo
                                                                                .getSort()),
                                                targetType);
                                if (accessOperator == cetus.hir.AccessOperator.MEMBER_ACCESS)
                                        return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.MemberAccess(
                                                        subExpressionConverted,
                                                        memberReference);
                                else
                                        return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.MemberPointerAccess(
                                                        subExpressionConverted,
                                                        memberReference);
                        }
                        // If schema member accessor
                        if (memberExpression instanceof MemberSVWrapper) {
                                if (accessOperator == cetus.hir.AccessOperator.MEMBER_ACCESS)
                                        return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.MemberAccess(
                                                        subExpressionConverted,
                                                        ((MemberSVWrapper) memberExpression)
                                                                        .getSV());
                                else
                                        return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.MemberPointerAccess(
                                                        subExpressionConverted,
                                                        ((MemberSVWrapper) memberExpression)
                                                                        .getSV());
                        }

                } else if (expression instanceof cetus.hir.ArrayAccess) {
                        cetus.hir.ArrayAccess arrayAccessExpression = (cetus.hir.ArrayAccess) expression;
                        assert arrayAccessExpression.getNumIndices() == 1;

                        IClangExpression lhsConverted = convertExpression(arrayAccessExpression
                                        .getArrayName());
                        IClangExpression rhsConverted = convertExpression(arrayAccessExpression
                                        .getIndex(0));

                        KeYJavaType lhsTypePair = getExpressionType(lhsConverted);
                        if (lhsTypePair != null
                                        && !(lhsTypePair.getJavaType() instanceof ArrayType))
                                lhsConverted = ensureValueExpression(lhsConverted);

                        return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.ArrayAccess(
                                        lhsConverted,
                                        ensureValueExpression(rhsConverted));
                } else if (expression instanceof cetus.hir.AssignmentExpression
                                && ((cetus.hir.AssignmentExpression) expression)
                                                .getOperator() == cetus.hir.AssignmentOperator.NORMAL) {
                        cetus.hir.AssignmentExpression assignmentExpression = (cetus.hir.AssignmentExpression) expression;

                        IClangExpression lhsConverted = convertExpression(assignmentExpression
                                        .getLHS());
                        IClangExpression rhsConverted = convertExpression(assignmentExpression
                                        .getRHS());
                        return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.ValueAssignment(
                                        ensureValueExpression(lhsConverted),
                                        ensureValueExpression(rhsConverted));
                } else if (expression instanceof de.uka.ilkd.key.lang.clang.common.loader.util.ReferenceAssignmentExpression) {
                        de.uka.ilkd.key.lang.clang.common.loader.util.ReferenceAssignmentExpression referenceAssignmentExpression = (de.uka.ilkd.key.lang.clang.common.loader.util.ReferenceAssignmentExpression) expression;
                        IClangExpression lhsConverted = convertExpression(referenceAssignmentExpression
                                        .getLHS());
                        IClangExpression rhsConverted = convertExpression(referenceAssignmentExpression
                                        .getRHS());
                        return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.ReferenceAssignment(
                                        lhsConverted, rhsConverted);
                } else if (expression instanceof cetus.hir.BinaryExpression) {
                        cetus.hir.BinaryExpression binaryExpression = (cetus.hir.BinaryExpression)expression;
                        cetus.hir.BinaryOperator operator = binaryExpression
                                        .getOperator();
                        
                        IClangExpression lhsConverted = convertExpression(binaryExpression
                                        .getLHS());
                        IClangExpression rhsConverted = convertExpression(binaryExpression
                                        .getRHS());

                        if (operator == cetus.hir.BinaryOperator.COMPARE_EQ)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.Equals(
                                                ensureValueExpression(lhsConverted),
                                                ensureValueExpression(rhsConverted),
                                                platform.getIntegerTypePair(platform.getSINTId())
                                                );
                        else if (operator == cetus.hir.BinaryOperator.COMPARE_NE)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.NotEquals(
                                                ensureValueExpression(lhsConverted),
                                                ensureValueExpression(rhsConverted),
                                                platform.getIntegerTypePair(platform.getSINTId())
                                                );
                        else if (operator == cetus.hir.BinaryOperator.LOGICAL_AND)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.logic.And(
                                                ensureValueExpression(lhsConverted),
                                                ensureValueExpression(rhsConverted),
                                                platform.getIntegerTypePair(platform.getSINTId())
                                                );
                        else if (operator == cetus.hir.BinaryOperator.LOGICAL_OR)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.logic.Or(
                                                ensureValueExpression(lhsConverted),
                                                ensureValueExpression(rhsConverted),
                                                platform.getIntegerTypePair(platform.getSINTId())
                                                );
                        else if (operator == cetus.hir.BinaryOperator.COMPARE_LT)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.relational.Less(
                                                ensureValueExpression(lhsConverted),
                                                ensureValueExpression(rhsConverted),
                                                platform.getIntegerTypePair(platform.getSINTId())
                                                );
                        else if (operator == cetus.hir.BinaryOperator.COMPARE_LE)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.relational.LessEq(
                                                ensureValueExpression(lhsConverted),
                                                ensureValueExpression(rhsConverted),
                                                platform.getIntegerTypePair(platform.getSINTId())
                                                );
                        else if (operator == cetus.hir.BinaryOperator.COMPARE_GT)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.relational.Greater(
                                                ensureValueExpression(lhsConverted),
                                                ensureValueExpression(rhsConverted),
                                                platform.getIntegerTypePair(platform.getSINTId())
                                                );
                        else if (operator == cetus.hir.BinaryOperator.COMPARE_GE)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.relational.GreaterEq(
                                                ensureValueExpression(lhsConverted),
                                                ensureValueExpression(rhsConverted),
                                                platform.getIntegerTypePair(platform.getSINTId())
                                                );
                        else if (operator == cetus.hir.BinaryOperator.ADD)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Plus(
                                                ensureValueExpression(lhsConverted),
                                                ensureValueExpression(rhsConverted));
                        else if (operator == cetus.hir.BinaryOperator.SUBTRACT) {
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Minus(
                                                ensureValueExpression(lhsConverted),
                                                ensureValueExpression(rhsConverted),
                                                castTypePair);
                        } else if (operator == cetus.hir.BinaryOperator.MULTIPLY)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Multiply(
                                                ensureValueExpression(lhsConverted),
                                                ensureValueExpression(rhsConverted));
                        else if (operator == cetus.hir.BinaryOperator.DIVIDE)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Divide(
                                                ensureValueExpression(lhsConverted),
                                                ensureValueExpression(rhsConverted));
                        else if (operator == cetus.hir.BinaryOperator.MODULUS)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Modulus(
                                                ensureValueExpression(lhsConverted),
                                                ensureValueExpression(rhsConverted));
                        else
                                throw buildConvertException(
                                                "Unsupported operator",
                                                expression);
                } else if (expression instanceof cetus.hir.UnaryExpression) {
                        cetus.hir.UnaryExpression unaryExpression = (cetus.hir.UnaryExpression) expression;
                        cetus.hir.UnaryOperator op = unaryExpression
                                        .getOperator();
                        cetus.hir.Expression subExpression = unaryExpression
                                        .getExpression();
                        IClangExpression subExpressionConverted = convertExpression(subExpression);

                        if (op == cetus.hir.UnaryOperator.ADDRESS_OF)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.AddressOf(
                                                subExpressionConverted);
                        else if (op == cetus.hir.UnaryOperator.DEREFERENCE)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.Dereference(
                                                ensureValueExpression(subExpressionConverted));
                        else if (op == cetus.hir.UnaryOperator.LOGICAL_NEGATION)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.logic.Not(
                                                ensureValueExpression(subExpressionConverted),
                                                platform.getIntegerTypePair(platform.getSINTId())
                                                );
                        else if (op == cetus.hir.UnaryOperator.MINUS)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Negative(
                                                ensureValueExpression(subExpressionConverted));
                        else if (op == cetus.hir.UnaryOperator.PLUS)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Positive(
                                                ensureValueExpression(subExpressionConverted));
                        else if (op == cetus.hir.UnaryOperator.PRE_INCREMENT)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.IncrementPrefix(
                                                subExpressionConverted);
                        else if (op == cetus.hir.UnaryOperator.PRE_DECREMENT)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.DecrementPrefix(
                                                subExpressionConverted);
                        else if (op == cetus.hir.UnaryOperator.POST_INCREMENT)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.IncrementPostfix(
                                                subExpressionConverted);
                        else if (op == cetus.hir.UnaryOperator.POST_DECREMENT)
                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.DecrementPostfix(
                                                subExpressionConverted);
                        else
                                throw buildConvertException(
                                                "Unsupported operator",
                                                expression);
                } else if (expression instanceof cetus.hir.Typecast) {
                        cetus.hir.Typecast typecast = (cetus.hir.Typecast) expression;
                        if (readHiddenField(typecast, "kind") == cetus.hir.Typecast.NORMAL) {
                                List specs = (List) readHiddenField(typecast,
                                                "specs");

                                de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference typeReference = convertTypeName(
                                                specs, true, typecast);

                                cetus.hir.Expression subExpression = (cetus.hir.Expression) typecast
                                                .getChildren().get(0);
                                IClangExpression subExpressionConverted = convertExpression(
                                                subExpression,
                                                typeReference instanceof ProgramSV ? null
                                                                : typeReference
                                                                                .getTypePair());

                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.TypeCast(
                                                ensureValueExpression(subExpressionConverted),
                                                typeReference);
                        }
                } else if (expression instanceof cetus.hir.ConditionalExpression) {
                        cetus.hir.ConditionalExpression conditional = (cetus.hir.ConditionalExpression) expression;

                        cetus.hir.Expression subExpression0 = conditional
                                        .getCondition();
                        IClangExpression subExpression0Converted = convertExpression(subExpression0);

                        cetus.hir.Expression subExpression1 = conditional
                                        .getTrueExpression();
                        IClangExpression subExpression1Converted = convertExpression(subExpression1);

                        cetus.hir.Expression subExpression2 = conditional
                                        .getFalseExpression();
                        IClangExpression subExpression2Converted = convertExpression(subExpression2);

                        return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.Conditional(
                                        ensureValueExpression(subExpression0Converted),
                                        ensureValueExpression(subExpression1Converted),
                                        ensureValueExpression(subExpression2Converted));
                } else if (expression instanceof cetus.hir.FunctionCall) {
                        cetus.hir.FunctionCall functionCall = (cetus.hir.FunctionCall) expression;

                        // If malloc call
                        if (functionCall.getName() instanceof cetus.hir.Identifier
                                        && ((cetus.hir.Identifier) functionCall
                                                        .getName()).getName()
                                                        .equals("malloc")
                                        && functionCall.getNumArguments() == 1) {
                                if (functionCall.getArgument(0) instanceof cetus.hir.SizeofExpression) {
                                        cetus.hir.SizeofExpression sizeofExpression = (cetus.hir.SizeofExpression) functionCall
                                                        .getArgument(0);
                                        LinkedList specs = (LinkedList) readHiddenField(
                                                        sizeofExpression,
                                                        "specs");
                                        de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference typeReference = convertTypeName(
                                                        specs, false,
                                                        sizeofExpression);

                                        return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.memory.Malloc(
                                                        typeReference,
                                                        platform.getPointerTypePair(platform.getVoidTypePair()));
                                } else
                                        throw buildConvertException(
                                                        "Unsupported malloc format",
                                                        expression);
                        }
                        // If calloc call
                        else if (functionCall.getName() instanceof cetus.hir.Identifier
                                        && ((cetus.hir.Identifier) functionCall
                                                        .getName()).getName()
                                                        .equals("calloc")
                                        && functionCall.getNumArguments() == 2) {
                                if (functionCall.getArgument(1) instanceof cetus.hir.SizeofExpression) {
                                        cetus.hir.SizeofExpression sizeofExpression = (cetus.hir.SizeofExpression) functionCall
                                                        .getArgument(1);
                                        LinkedList specs = (LinkedList) readHiddenField(
                                                        sizeofExpression,
                                                        "specs");
                                        de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference typeReference = convertTypeName(
                                                        specs, false,
                                                        sizeofExpression);

                                        cetus.hir.Expression subExpression = functionCall
                                                        .getArgument(0);
                                        IClangExpression subExpressionConverted = convertExpression(subExpression);

                                        return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.memory.Calloc(
                                                        ensureValueExpression(subExpressionConverted),
                                                        typeReference,
                                                        platform.getPointerTypePair(platform.getVoidTypePair())
                                                        );
                                } else
                                        throw buildConvertException(
                                                        "Unsupported calloc format",
                                                        expression);
                        }
                        // If free call
                        else if (functionCall.getName() instanceof cetus.hir.Identifier
                                        && ((cetus.hir.Identifier) functionCall
                                                        .getName()).getName()
                                                        .equals("free")
                                        && functionCall.getNumArguments() == 1) {
                                cetus.hir.Expression subExpression = functionCall
                                                .getArgument(0);
                                IClangExpression subExpressionConverted = convertExpression(subExpression);

                                return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.memory.Free(
                                                ensureValueExpression(subExpressionConverted),
                                                platform.getVoidTypePair()
                                                );
                        }
                        // Regular function call
                        else
                                throw buildConvertException(
                                                "Function calls not supported",
                                                expression);

                } else if (expression instanceof cetus.hir.CommaExpression) {
                        cetus.hir.CommaExpression commaExpression = (cetus.hir.CommaExpression) expression;

                        List children = commaExpression.getChildren();
                        IClangExpression expressionConverted = convertExpression((cetus.hir.Expression) children
                                        .get(0));
                        for (int i = 1; i < children.size(); i++) {
                                IClangExpression subExpressionConverted = convertExpression((cetus.hir.Expression) children
                                                .get(i));
                                expressionConverted = new de.uka.ilkd.key.lang.clang.common.program.expression.operator.Comma(
                                                expressionConverted,
                                                subExpressionConverted);
                        }
                        return expressionConverted;
                } else if (expression instanceof de.uka.ilkd.key.lang.clang.common.loader.util.MetaExpression) {
                        de.uka.ilkd.key.lang.clang.common.loader.util.MetaExpression metaExpression = (de.uka.ilkd.key.lang.clang.common.loader.util.MetaExpression) expression;
                        ArrayOfBaseProgramSV arguments = new ArrayOfBaseProgramSV(
                                        metaExpression.getArguments());
                        IClangProgramMeta metaConstruct= configuration
                                        .getProgramMetaConstruct(
                                                        new Name(
                                                                        metaExpression
                                                                                        .getName()), arguments);

                        if (metaConstruct == null)
                                throw buildConvertException(
                                                "Program meta construct does not exist",
                                                expression);

                        if (!(metaConstruct instanceof IClangExpression))
                                throw buildConvertException(
                                                "Program meta construct '"
                                                                + metaExpression
                                                                                .getName()
                                                                + "' cannot be used as a expression",
                                                expression);

                        return (IClangExpression) metaConstruct;
                }

                throw buildConvertException("Unsupported expression format",
                                expression);
        }

        private de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference convertTypeName(
                        List specs, boolean extractValueType,
                        cetus.hir.Printable parent) throws ConversionException {
                // If schema type name
                if (specs.size() == 1 && specs.get(0) instanceof TypeSVWrapper) {
                        TypeProgramSV typeSV = ((TypeSVWrapper) specs.get(0))
                                        .getSV();
                        return typeSV;
                }
                // Normal type name
                else {
                        cetus.hir.Declarator declarator = null;

                        if (specs.size() > 0
                                        && specs.get(specs.size() - 1) instanceof cetus.hir.Declarator) {
                                declarator = (cetus.hir.Declarator) specs
                                                .get(specs.size() - 1);
                                specs = specs.subList(0, specs.size() - 1);
                        }

                        KeYJavaType specifierTypePair = computeTypeFromSpecifiers(
                                        specs, parent);
                        KeYJavaType typePair = declarator != null ? computeTypeFromDeclarator(
                                        declarator, specifierTypePair)
                                        : specifierTypePair;

                        if (extractValueType) {
                                typePair = TypePairUtil.extractFromScalarType(typePair);
                                if (typePair == null)
                                        throw buildConvertException(
                                                        "Expecting a scalar type name",
                                                        parent);
                        }
                        return new de.uka.ilkd.key.lang.clang.common.program.type.TypeReference(typePair);
                }

        }

        private KeYJavaType getExpressionType(IClangExpression expression) {
                KeYJavaType type = ClangExpressionUtil.getTypePair(expression,
                                configuration.getEnvironment());
                return type;
        }

        private IClangExpression ensureValueExpression(IClangExpression expression) {

                KeYJavaType type = getExpressionType(expression);
                if (type != null && type.getJavaType() instanceof ScalarType)
                        return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.ValueOf(
                                        expression);
                else if (type != null
                                && type.getJavaType() instanceof ArrayType)
                        return new de.uka.ilkd.key.lang.clang.common.program.expression.operator.AddressOf(
                                        new de.uka.ilkd.key.lang.clang.common.program.expression.operator.ArrayAccess(
                                                        expression,
                                                        new de.uka.ilkd.key.lang.clang.common.program.expression.literal.IntegerLiteral(
                                                                        BigInteger
                                                                                        .valueOf(0),
                                                                                        platform.getIntegerTypePair(platform.getSINTId()))));
                else
                        return expression;
        }

        private static Object readHiddenField(Object object, String name) {
                try {
                        Field field = object.getClass().getDeclaredField(name);
                        field.setAccessible(true);
                        return field.get(object);
                } catch (Exception e) {
                        throw new RuntimeException(e);
                }
        }

        /**
         * Initializes the state of block entering/leaving protocol.
         * 
         */
        private void initBlockProtocol() {
                blockVariableNS = new Namespace();
                blockRenamedVariableNS = new Namespace();
        }

        /**
         * Enters program block. Sets up block configuration.
         */
        private void enterBlock() {
                blockVariableNS = new Namespace(blockVariableNS);
                blockRenamedVariableNS = new Namespace(blockRenamedVariableNS);
        }

        /**
         * Leaves program block. Restores the previous block configuration.
         */
        private void leaveBlock() {
                blockRenamedVariableNS = blockRenamedVariableNS.parent();
                blockVariableNS = blockVariableNS.parent();
        }

        /**
         * Tests if variable needs renaming because of clashing with some other
         * variable name.
         * 
         * @param name
         * @return
         */
        private boolean isBlockVariableClashing(Name name) {
                return blockVariableNS.lookup(name) != null;
        }

        /**
         * Tests if the variable name is defined for the second time in the
         * block (which is prohibited).
         * 
         * @param name
         * @return
         */
        private boolean isBlockVariableDuplicate(Name name) {
                return blockRenamedVariableNS.lookupLocally(name) != null;
        }

        /**
         * Registeres possibly renamed variable in the block configuration.
         * 
         * @param realName
         * @param variable
         */
        private void registerBlockVariable(Name realName,
                        IClangVariable variable) {
                blockVariableNS.add(variable);
                blockRenamedVariableNS.add(new RenamedVariable(realName,
                                variable));
        }

        /**
         * Looks up variable by its real name (can be either global variable or
         * block variable).
         * 
         * @param realName
         * @return
         */
        private IClangVariable lookupVariable(Name realName) {
                // Look for block variable
                RenamedVariable renamedVariable = (RenamedVariable) blockRenamedVariableNS
                                .lookup(realName);
                if (renamedVariable != null)
                        return ((RenamedVariable) renamedVariable).variable;

                // Look for global variable
                if (programVariableNS != null)
                        return (IClangVariable) (programVariableNS
                                        .lookup(realName));
                else
                        return null;
        }

        /**
         * Builds a program variable name that is unique with respect to the
         * current block and its parents.
         */
        private Name buildBlockUniqueVariableName(Name name) {
                // Try appending ascending counter until the name is unique
                for (int i = 1; true; i++) {
                        Name newName = buildVariableName(name
                                        .toString()
                                        + "_" + i);
                        if (blockVariableNS.lookup(newName) == null)
                                return newName;
                }
        }

        /**
         * Builds variable name from string representation.
         * 
         * @param name
         * @return
         */
        Name buildVariableName(String name) {
                return configuration.getEnvironment().getLangServicesEnv()
                                .formatVariableName(name);
        }

        /**
         * Represents a variable paired with its real name before renaming.
         * However, the names can be equal, if the renaming did not take place.
         * 
         * @author oleg.myrk@gmail.com
         */
        private class RenamedVariable implements Named {
                Name realName;

                IClangVariable variable;

                RenamedVariable(Name realName,
                                IClangVariable variable) {
                        this.realName = realName;
                        this.variable = variable;
                }

                public Name name() {
                        return realName;
                }
        }

        private LoadingContext getContext(cetus.hir.Printable element) {
                // TODO: Correct behavior depends on the platform's default character encoding 
                // and consequently works reliably only with the first 128 unicode characters.
                // However, this limitation comes from Cetus and there is nothing we can do.
                // @author oleg.myrk@gmail.com
                ByteArrayOutputStream baos = new ByteArrayOutputStream();
                element.print(new PrintStream(baos));
                return new LoadingContext(currentContext
                                .getFileName(), baos.toString(),
                                currentContext.getSource());
        }

        /**
         * Builds convert exception from error message and the program element
         * that is the subject of the message. TODO: currently there is no
         * position information in Cetus objects.
         * 
         * @param message
         * @param element
         * @return
         */
        private ConversionException buildConvertException(String message,
                        cetus.hir.Printable element) {
                return new ConversionException(message, getContext(element));
        }
}
