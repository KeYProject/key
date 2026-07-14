public class Textblock {

    // Expected One large string w/o newlines
    String text = """
            Lorem ipsum dolor sit amet, consectetur adipiscing \
            elit, sed do eiusmod tempor incididunt ut labore \
            et dolore magna aliqua.\
            """;

    // Expected: strip indentation and new lines. Four spaces before <body>.
    String html = """
            <html>
                <body>
                    <p>Hello, world</p>
                </body>
            </html>
            """;

    // Expected: String with newlines and escaped quotes.
    String query = """
            SELECT "EMP_ID", "LAST_NAME" FROM "EMPLOYEE_TB"
            WHERE "CITY" = 'INDIANAPOLIS'
            ORDER BY "EMP_ID", "LAST_NAME";
            """;

    Object obj = ("""
            function hello() {
                print('"Hello, world"');
            }""")+
            """
            hello();
            """;

    //expected "line 1\nlines 2\nline 3\n"
    String simple = """
            line 1
            line 2
            line 3
            """;

    //Expected: newlines and escaped quotes
    String code =
            """
                    String text = \"""
                        A text block inside a text block
                    \""";
                    """;

    String abc = ("""
                 1 "
                 2 ""
                 3 ""\"
                 4 ""\""
                 5 ""\"""
                 6 ""\"""\"
                 7 ""\"""\""
                 8 ""\"""\"""
                 9 ""\"""\"""\"
                10 ""\"""\"""\""
                11 ""\"""\"""\"""
                12 ""\"""\"""\"""\"
            """);

    String text = """
            Lorem ipsum dolor sit amet, consectetur adipiscing \
            elit, sed do eiusmod tempor incididunt ut labore \
            et dolore magna aliqua.\
            """;

    String colors = """
            red  \s
            green\s
            blue \s
            """;

    // attention trailing whitespaces!
    String colors = """
            red      
            green     
            blue      
            """;

}