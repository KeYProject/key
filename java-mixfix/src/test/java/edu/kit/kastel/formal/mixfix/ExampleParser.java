package de.uka.iti.mixfix.test;


//public class ExampleParser {
//
//    private static MixFixParser<String, String> parser;
//    private static MixFixRuleCollection<String, String> coll;
//
//    public static void main(String[] args) throws IOException {
//        coll = new MixFixRuleCollection<String, String>();
//        TestMixFixParser.addComplexGrammar(coll);
//        parser = new MixFixParser<String,String>(coll);
//        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
//        String line =  br.readLine();
//        while(line != null && line.length() > 0) {
//            try {
//                String result = parser.parseExpression(Arrays.asList(line.split(" +")));
//                System.out.println(result);
//            } catch (MixFixException e) {
//                System.err.println(e);
//                System.err.println(e.getToken());
//                // System.err.println(e.getPosition());
//            }
//            line =  br.readLine();
//        }
//    }
//
//}
