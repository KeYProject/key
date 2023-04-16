package de.uka.ilkd.key.java;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.BlockStmt;

import java.io.Reader;

/**
 * @author Alexander Weigl
 * @version 1 (05.03.22)
 */
public class JavaParserFactory {
    private final JavaService javaService;

    public JavaParserFactory(JavaService javaService) {
        this.javaService = javaService;
    }

    public ParseResult<CompilationUnit> parseCompilationUnit(Reader reader) {
        return javaService.createJavaParser().parse(reader);
    }

    public ParseResult<BlockStmt> parseStatementBlock(String sr) {
        return javaService.createJavaParser().parseBlock(sr);
    }
}
