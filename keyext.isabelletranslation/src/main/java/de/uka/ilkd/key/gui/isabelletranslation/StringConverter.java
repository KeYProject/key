//
// Source code recreated from a .class file by IntelliJ IDEA
// (powered by FernFlower decompiler)
//

package de.uka.ilkd.key.gui.isabelletranslation;

import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.mlvalue.MLValue;
import de.unruh.isabelle.mlvalue.StringConverter$;
import scala.concurrent.Future;
import scala.reflect.ScalaSignature;

@ScalaSignature(
        bytes = "\u0006\u0005};Q\u0001C\u0005\t\u0002I1Q\u0001F\u0005\t\u0002UAQAM\u0001\u0005\u0002MBQ\u0001N\u0001\u0005BUBQ\u0001S\u0001\u0005B%CQ\u0001V\u0001\u0005BUCQ\u0001W\u0001\u0005BeCQ\u0001X\u0001\u0005Bu\u000bqb\u0015;sS:<7i\u001c8wKJ$XM\u001d\u0006\u0003\u0015-\tq!\u001c7wC2,XM\u0003\u0002\r\u001b\u0005A\u0011n]1cK2dWM\u0003\u0002\u000f\u001f\u0005)QO\u001c:vQ*\t\u0001#\u0001\u0002eK\u000e\u0001\u0001CA\n\u0002\u001b\u0005I!aD*ue&twmQ8om\u0016\u0014H/\u001a:\u0014\u0005\u00051\u0002cA\f&Q9\u0011\u0001d\t\b\u00033\tr!AG\u0011\u000f\u0005m\u0001cB\u0001\u000f \u001b\u0005i\"B\u0001\u0010\u0012\u0003\u0019a$o\\8u}%\t\u0001#\u0003\u0002\u000f\u001f%\u0011A\"D\u0005\u0003\u0015-I!\u0001J\u0005\u0002\u000f5ce+\u00197vK&\u0011ae\n\u0002\n\u0007>tg/\u001a:uKJT!\u0001J\u0005\u0011\u0005%zcB\u0001\u0016.!\ta2FC\u0001-\u0003\u0015\u00198-\u00197b\u0013\tq3&\u0001\u0004Qe\u0016$WMZ\u0005\u0003aE\u0012aa\u0015;sS:<'B\u0001\u0018,\u0003\u0019a\u0014N\\5u}Q\t!#A\u0003ti>\u0014X\r\u0006\u00027\u0003R\u0011qG\u000f\t\u0004'aB\u0013BA\u001d\n\u0005\u001diEJV1mk\u0016DQ\u0001D\u0002A\u0004m\u0002\"\u0001P \u000e\u0003uR!AP\u0006\u0002\u000f\r|g\u000e\u001e:pY&\u0011\u0001)\u0010\u0002\t\u0013N\f'-\u001a7mK\")!i\u0001a\u0001Q\u0005)a/\u00197vK\"\u00121\u0001\u0012\t\u0003\u000b\u001ak\u0011aK\u0005\u0003\u000f.\u0012a!\u001b8mS:,\u0017\u0001\u0003:fiJLWM^3\u0015\u0005)\u0013FCA&R!\rau\nK\u0007\u0002\u001b*\u0011ajK\u0001\u000bG>t7-\u001e:sK:$\u0018B\u0001)N\u0005\u00191U\u000f^;sK\")A\u0002\u0002a\u0002w!)!\t\u0002a\u0001o!\u0012A\u0001R\u0001\u000bKbtGk\u001c,bYV,GC\u0001\u0015W\u0011\u0015aQ\u0001q\u0001<Q\t)A)\u0001\u0006wC2,X\rV8Fq:$\"\u0001\u000b.\t\u000b11\u00019A\u001e)\u0005\u0019!\u0015AB7m)f\u0004X\r\u0006\u0002)=\")Ab\u0002a\u0002w\u0001"
)
public final class StringConverter extends MLValue.Converter<String> {
    public String mlType(final Isabelle isabelle) {
        return StringConverter$.MODULE$.mlType(isabelle);
    }

    public String valueToExn(final Isabelle isabelle) {
        return StringConverter$.MODULE$.valueToExn(isabelle);
    }

    public String exnToValue(final Isabelle isabelle) {
        return StringConverter$.MODULE$.exnToValue(isabelle);
    }

    public Future<String> retrieve(final MLValue<String> value, final Isabelle isabelle) {
        return StringConverter$.MODULE$.retrieve(value, isabelle);
    }

    public MLValue<String> store(final String value, final Isabelle isabelle) {
        return StringConverter$.MODULE$.store(value, isabelle);
    }
}