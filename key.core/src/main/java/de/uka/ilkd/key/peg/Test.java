package de.uka.ilkd.key.peg;

import org.parboiled.Parboiled;
import org.parboiled.errors.InvalidInputError;
import org.parboiled.parserunners.ReportingParseRunner;
import org.parboiled.support.ParsingResult;

/**
 *
 * @author Alexander Weigl
 * @version 1 (25.06.26)
 */
public class Test {

    public static void main(String[] args) {
        var p = Parboiled.createParser(KeYParboiledParser.class);

        final var intX = new ReportingParseRunner<>(p.OneBoundVariable()).run("int x");
        ((InvalidInputError)intX.parseErrors.getFirst()).getFailedMatchers().forEach(System.out::println);
        System.out.println(intX.matched);


        System.out.println(new ReportingParseRunner<>(p.OpNot()).run("!").matched);
        System.out.println(new ReportingParseRunner<>(p.Term60()).run("!x").matched);

        ParsingResult<Object> result
                = new ReportingParseRunner<>(p.Problem()).run(
                """
                        \\problem{
                            (true & true
                        }
                        """

        );
        System.out.println(result.matched);
        System.out.println(result.parseErrors.getFirst().getErrorMessage());
        System.out.println(result.parseErrors.getFirst().getStartIndex());
        System.out.println(result.parseErrors.getFirst().getEndIndex());
        ((InvalidInputError) result.parseErrors.getFirst()).getFailedMatchers()
                .stream().map(
                        it -> it.getElementAtLevel(it.length() - 1).matcher
                )
                .forEach(System.out::println);

        System.out.println(result);
    }
}
