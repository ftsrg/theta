// Generated from /home/levente/Documents/University/theta-refactor/subprojects/frontends/litmus2xcfa/src/main/antlr/LitmusAssertions.g4 by ANTLR 4.9.3
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class LitmusAssertionsLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.9.3", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		AssertionListExpectationTest=1, AssertionAnd=2, AssertionOr=3, AssertionExists=4, 
		AssertionFinal=5, AssertionForall=6, AssertionFilter=7, AssertionNot=8, 
		AssertionWith=9, ThreadIdentifier=10, EqualsEquals=11, NotEquals=12, LessEquals=13, 
		GreaterEquals=14, Identifier=15, DigitSequence=16, Whitespace=17, Newline=18, 
		BlockComment=19, ExecConfig=20, Excl=21, Quot=22, Num=23, Dollar=24, Percent=25, 
		Amp=26, Apos=27, LPar=28, RPar=29, Ast=30, Plus=31, Comma=32, Minus=33, 
		Period=34, Slash=35, Colon=36, Semi=37, Less=38, Equals=39, Greater=40, 
		Question=41, At=42, LBracket=43, RBracket=44, BSlash=45, LBrace=46, RBrace=47, 
		Circ=48, Tilde=49, Bar=50, Underscore=51;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"AssertionListExpectationTest", "AssertionAnd", "AssertionOr", "AssertionExists", 
			"AssertionFinal", "AssertionForall", "AssertionFilter", "AssertionNot", 
			"AssertionWith", "ThreadIdentifier", "EqualsEquals", "NotEquals", "LessEquals", 
			"GreaterEquals", "Identifier", "DigitSequence", "Digit", "Letter", "Whitespace", 
			"Newline", "BlockComment", "ExecConfig", "Excl", "Quot", "Num", "Dollar", 
			"Percent", "Amp", "Apos", "LPar", "RPar", "Ast", "Plus", "Comma", "Minus", 
			"Period", "Slash", "Colon", "Semi", "Less", "Equals", "Greater", "Question", 
			"At", "LBracket", "RBracket", "BSlash", "LBrace", "RBrace", "Circ", "Tilde", 
			"Bar", "Underscore"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, null, "'/\\'", "'\\/'", "'exists'", "'final'", "'forall'", "'filter'", 
			null, "'with'", null, "'=='", "'!='", "'<='", "'>='", null, null, null, 
			null, null, null, "'!'", "'\"'", "'#'", "'$'", "'%'", "'&'", "'''", "'('", 
			"')'", "'*'", "'+'", "','", "'-'", "'.'", "'/'", "':'", "';'", "'<'", 
			"'='", "'>'", "'?'", "'@'", "'['", "']'", "'\\'", "'{'", "'}'", "'^'", 
			"'~'", "'|'", "'_'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "AssertionListExpectationTest", "AssertionAnd", "AssertionOr", 
			"AssertionExists", "AssertionFinal", "AssertionForall", "AssertionFilter", 
			"AssertionNot", "AssertionWith", "ThreadIdentifier", "EqualsEquals", 
			"NotEquals", "LessEquals", "GreaterEquals", "Identifier", "DigitSequence", 
			"Whitespace", "Newline", "BlockComment", "ExecConfig", "Excl", "Quot", 
			"Num", "Dollar", "Percent", "Amp", "Apos", "LPar", "RPar", "Ast", "Plus", 
			"Comma", "Minus", "Period", "Slash", "Colon", "Semi", "Less", "Equals", 
			"Greater", "Question", "At", "LBracket", "RBracket", "BSlash", "LBrace", 
			"RBrace", "Circ", "Tilde", "Bar", "Underscore"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}


	public LitmusAssertionsLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "LitmusAssertions.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\65\u0141\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31"+
		"\t\31\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t"+
		" \4!\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t"+
		"+\4,\t,\4-\t-\4.\t.\4/\t/\4\60\t\60\4\61\t\61\4\62\t\62\4\63\t\63\4\64"+
		"\t\64\4\65\t\65\4\66\t\66\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2"+
		"\3\2\3\2\3\2\3\2\3\2\3\2\5\2\177\n\2\3\3\3\3\3\3\3\4\3\4\3\4\3\5\3\5\3"+
		"\5\3\5\3\5\3\5\3\5\3\6\3\6\3\6\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3\7\3\7\3\7"+
		"\3\b\3\b\3\b\3\b\3\b\3\b\3\b\3\t\3\t\3\t\3\t\5\t\u00a6\n\t\3\n\3\n\3\n"+
		"\3\n\3\n\3\13\3\13\3\13\3\f\3\f\3\f\3\r\3\r\3\r\3\16\3\16\3\16\3\17\3"+
		"\17\3\17\3\20\7\20\u00bd\n\20\f\20\16\20\u00c0\13\20\3\20\6\20\u00c3\n"+
		"\20\r\20\16\20\u00c4\3\20\3\20\3\20\7\20\u00ca\n\20\f\20\16\20\u00cd\13"+
		"\20\3\21\6\21\u00d0\n\21\r\21\16\21\u00d1\3\22\3\22\3\23\3\23\3\24\6\24"+
		"\u00d9\n\24\r\24\16\24\u00da\3\24\3\24\3\25\3\25\5\25\u00e1\n\25\3\25"+
		"\5\25\u00e4\n\25\3\25\3\25\3\26\3\26\3\26\3\26\7\26\u00ec\n\26\f\26\16"+
		"\26\u00ef\13\26\3\26\3\26\3\26\3\26\3\26\3\27\3\27\3\27\3\27\7\27\u00fa"+
		"\n\27\f\27\16\27\u00fd\13\27\3\27\3\27\3\27\3\27\3\27\3\30\3\30\3\31\3"+
		"\31\3\32\3\32\3\33\3\33\3\34\3\34\3\35\3\35\3\36\3\36\3\37\3\37\3 \3 "+
		"\3!\3!\3\"\3\"\3#\3#\3$\3$\3%\3%\3&\3&\3\'\3\'\3(\3(\3)\3)\3*\3*\3+\3"+
		"+\3,\3,\3-\3-\3.\3.\3/\3/\3\60\3\60\3\61\3\61\3\62\3\62\3\63\3\63\3\64"+
		"\3\64\3\65\3\65\3\66\3\66\4\u00ed\u00fb\2\67\3\3\5\4\7\5\t\6\13\7\r\b"+
		"\17\t\21\n\23\13\25\f\27\r\31\16\33\17\35\20\37\21!\22#\2%\2\'\23)\24"+
		"+\25-\26/\27\61\30\63\31\65\32\67\339\34;\35=\36?\37A C!E\"G#I$K%M&O\'"+
		"Q(S)U*W+Y,[-]._/a\60c\61e\62g\63i\64k\65\3\2\5\3\2\62;\4\2C\\c|\4\2\13"+
		"\13\"\"\2\u014d\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3"+
		"\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2"+
		"\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3"+
		"\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3\2\2\2\2/\3\2\2\2\2\61\3"+
		"\2\2\2\2\63\3\2\2\2\2\65\3\2\2\2\2\67\3\2\2\2\29\3\2\2\2\2;\3\2\2\2\2"+
		"=\3\2\2\2\2?\3\2\2\2\2A\3\2\2\2\2C\3\2\2\2\2E\3\2\2\2\2G\3\2\2\2\2I\3"+
		"\2\2\2\2K\3\2\2\2\2M\3\2\2\2\2O\3\2\2\2\2Q\3\2\2\2\2S\3\2\2\2\2U\3\2\2"+
		"\2\2W\3\2\2\2\2Y\3\2\2\2\2[\3\2\2\2\2]\3\2\2\2\2_\3\2\2\2\2a\3\2\2\2\2"+
		"c\3\2\2\2\2e\3\2\2\2\2g\3\2\2\2\2i\3\2\2\2\2k\3\2\2\2\3~\3\2\2\2\5\u0080"+
		"\3\2\2\2\7\u0083\3\2\2\2\t\u0086\3\2\2\2\13\u008d\3\2\2\2\r\u0093\3\2"+
		"\2\2\17\u009a\3\2\2\2\21\u00a5\3\2\2\2\23\u00a7\3\2\2\2\25\u00ac\3\2\2"+
		"\2\27\u00af\3\2\2\2\31\u00b2\3\2\2\2\33\u00b5\3\2\2\2\35\u00b8\3\2\2\2"+
		"\37\u00be\3\2\2\2!\u00cf\3\2\2\2#\u00d3\3\2\2\2%\u00d5\3\2\2\2\'\u00d8"+
		"\3\2\2\2)\u00e3\3\2\2\2+\u00e7\3\2\2\2-\u00f5\3\2\2\2/\u0103\3\2\2\2\61"+
		"\u0105\3\2\2\2\63\u0107\3\2\2\2\65\u0109\3\2\2\2\67\u010b\3\2\2\29\u010d"+
		"\3\2\2\2;\u010f\3\2\2\2=\u0111\3\2\2\2?\u0113\3\2\2\2A\u0115\3\2\2\2C"+
		"\u0117\3\2\2\2E\u0119\3\2\2\2G\u011b\3\2\2\2I\u011d\3\2\2\2K\u011f\3\2"+
		"\2\2M\u0121\3\2\2\2O\u0123\3\2\2\2Q\u0125\3\2\2\2S\u0127\3\2\2\2U\u0129"+
		"\3\2\2\2W\u012b\3\2\2\2Y\u012d\3\2\2\2[\u012f\3\2\2\2]\u0131\3\2\2\2_"+
		"\u0133\3\2\2\2a\u0135\3\2\2\2c\u0137\3\2\2\2e\u0139\3\2\2\2g\u013b\3\2"+
		"\2\2i\u013d\3\2\2\2k\u013f\3\2\2\2mn\7v\2\2no\7u\2\2o\177\7q\2\2pq\7e"+
		"\2\2q\177\7e\2\2rs\7q\2\2st\7r\2\2tu\7v\2\2uv\7k\2\2v\177\7e\2\2wx\7f"+
		"\2\2xy\7g\2\2yz\7h\2\2z{\7c\2\2{|\7w\2\2|}\7n\2\2}\177\7v\2\2~m\3\2\2"+
		"\2~p\3\2\2\2~r\3\2\2\2~w\3\2\2\2\177\4\3\2\2\2\u0080\u0081\7\61\2\2\u0081"+
		"\u0082\7^\2\2\u0082\6\3\2\2\2\u0083\u0084\7^\2\2\u0084\u0085\7\61\2\2"+
		"\u0085\b\3\2\2\2\u0086\u0087\7g\2\2\u0087\u0088\7z\2\2\u0088\u0089\7k"+
		"\2\2\u0089\u008a\7u\2\2\u008a\u008b\7v\2\2\u008b\u008c\7u\2\2\u008c\n"+
		"\3\2\2\2\u008d\u008e\7h\2\2\u008e\u008f\7k\2\2\u008f\u0090\7p\2\2\u0090"+
		"\u0091\7c\2\2\u0091\u0092\7n\2\2\u0092\f\3\2\2\2\u0093\u0094\7h\2\2\u0094"+
		"\u0095\7q\2\2\u0095\u0096\7t\2\2\u0096\u0097\7c\2\2\u0097\u0098\7n\2\2"+
		"\u0098\u0099\7n\2\2\u0099\16\3\2\2\2\u009a\u009b\7h\2\2\u009b\u009c\7"+
		"k\2\2\u009c\u009d\7n\2\2\u009d\u009e\7v\2\2\u009e\u009f\7g\2\2\u009f\u00a0"+
		"\7t\2\2\u00a0\20\3\2\2\2\u00a1\u00a6\5g\64\2\u00a2\u00a3\7p\2\2\u00a3"+
		"\u00a4\7q\2\2\u00a4\u00a6\7v\2\2\u00a5\u00a1\3\2\2\2\u00a5\u00a2\3\2\2"+
		"\2\u00a6\22\3\2\2\2\u00a7\u00a8\7y\2\2\u00a8\u00a9\7k\2\2\u00a9\u00aa"+
		"\7v\2\2\u00aa\u00ab\7j\2\2\u00ab\24\3\2\2\2\u00ac\u00ad\7R\2\2\u00ad\u00ae"+
		"\5!\21\2\u00ae\26\3\2\2\2\u00af\u00b0\7?\2\2\u00b0\u00b1\7?\2\2\u00b1"+
		"\30\3\2\2\2\u00b2\u00b3\7#\2\2\u00b3\u00b4\7?\2\2\u00b4\32\3\2\2\2\u00b5"+
		"\u00b6\7>\2\2\u00b6\u00b7\7?\2\2\u00b7\34\3\2\2\2\u00b8\u00b9\7@\2\2\u00b9"+
		"\u00ba\7?\2\2\u00ba\36\3\2\2\2\u00bb\u00bd\5k\66\2\u00bc\u00bb\3\2\2\2"+
		"\u00bd\u00c0\3\2\2\2\u00be\u00bc\3\2\2\2\u00be\u00bf\3\2\2\2\u00bf\u00c2"+
		"\3\2\2\2\u00c0\u00be\3\2\2\2\u00c1\u00c3\5%\23\2\u00c2\u00c1\3\2\2\2\u00c3"+
		"\u00c4\3\2\2\2\u00c4\u00c2\3\2\2\2\u00c4\u00c5\3\2\2\2\u00c5\u00cb\3\2"+
		"\2\2\u00c6\u00ca\5%\23\2\u00c7\u00ca\5#\22\2\u00c8\u00ca\5k\66\2\u00c9"+
		"\u00c6\3\2\2\2\u00c9\u00c7\3\2\2\2\u00c9\u00c8\3\2\2\2\u00ca\u00cd\3\2"+
		"\2\2\u00cb\u00c9\3\2\2\2\u00cb\u00cc\3\2\2\2\u00cc \3\2\2\2\u00cd\u00cb"+
		"\3\2\2\2\u00ce\u00d0\5#\22\2\u00cf\u00ce\3\2\2\2\u00d0\u00d1\3\2\2\2\u00d1"+
		"\u00cf\3\2\2\2\u00d1\u00d2\3\2\2\2\u00d2\"\3\2\2\2\u00d3\u00d4\t\2\2\2"+
		"\u00d4$\3\2\2\2\u00d5\u00d6\t\3\2\2\u00d6&\3\2\2\2\u00d7\u00d9\t\4\2\2"+
		"\u00d8\u00d7\3\2\2\2\u00d9\u00da\3\2\2\2\u00da\u00d8\3\2\2\2\u00da\u00db"+
		"\3\2\2\2\u00db\u00dc\3\2\2\2\u00dc\u00dd\b\24\2\2\u00dd(\3\2\2\2\u00de"+
		"\u00e0\7\17\2\2\u00df\u00e1\7\f\2\2\u00e0\u00df\3\2\2\2\u00e0\u00e1\3"+
		"\2\2\2\u00e1\u00e4\3\2\2\2\u00e2\u00e4\7\f\2\2\u00e3\u00de\3\2\2\2\u00e3"+
		"\u00e2\3\2\2\2\u00e4\u00e5\3\2\2\2\u00e5\u00e6\b\25\2\2\u00e6*\3\2\2\2"+
		"\u00e7\u00e8\7*\2\2\u00e8\u00e9\7,\2\2\u00e9\u00ed\3\2\2\2\u00ea\u00ec"+
		"\13\2\2\2\u00eb\u00ea\3\2\2\2\u00ec\u00ef\3\2\2\2\u00ed\u00ee\3\2\2\2"+
		"\u00ed\u00eb\3\2\2\2\u00ee\u00f0\3\2\2\2\u00ef\u00ed\3\2\2\2\u00f0\u00f1"+
		"\7,\2\2\u00f1\u00f2\7+\2\2\u00f2\u00f3\3\2\2\2\u00f3\u00f4\b\26\2\2\u00f4"+
		",\3\2\2\2\u00f5\u00f6\7>\2\2\u00f6\u00f7\7>\2\2\u00f7\u00fb\3\2\2\2\u00f8"+
		"\u00fa\13\2\2\2\u00f9\u00f8\3\2\2\2\u00fa\u00fd\3\2\2\2\u00fb\u00fc\3"+
		"\2\2\2\u00fb\u00f9\3\2\2\2\u00fc\u00fe\3\2\2\2\u00fd\u00fb\3\2\2\2\u00fe"+
		"\u00ff\7@\2\2\u00ff\u0100\7@\2\2\u0100\u0101\3\2\2\2\u0101\u0102\b\27"+
		"\2\2\u0102.\3\2\2\2\u0103\u0104\7#\2\2\u0104\60\3\2\2\2\u0105\u0106\7"+
		"$\2\2\u0106\62\3\2\2\2\u0107\u0108\7%\2\2\u0108\64\3\2\2\2\u0109\u010a"+
		"\7&\2\2\u010a\66\3\2\2\2\u010b\u010c\7\'\2\2\u010c8\3\2\2\2\u010d\u010e"+
		"\7(\2\2\u010e:\3\2\2\2\u010f\u0110\7)\2\2\u0110<\3\2\2\2\u0111\u0112\7"+
		"*\2\2\u0112>\3\2\2\2\u0113\u0114\7+\2\2\u0114@\3\2\2\2\u0115\u0116\7,"+
		"\2\2\u0116B\3\2\2\2\u0117\u0118\7-\2\2\u0118D\3\2\2\2\u0119\u011a\7.\2"+
		"\2\u011aF\3\2\2\2\u011b\u011c\7/\2\2\u011cH\3\2\2\2\u011d\u011e\7\60\2"+
		"\2\u011eJ\3\2\2\2\u011f\u0120\7\61\2\2\u0120L\3\2\2\2\u0121\u0122\7<\2"+
		"\2\u0122N\3\2\2\2\u0123\u0124\7=\2\2\u0124P\3\2\2\2\u0125\u0126\7>\2\2"+
		"\u0126R\3\2\2\2\u0127\u0128\7?\2\2\u0128T\3\2\2\2\u0129\u012a\7@\2\2\u012a"+
		"V\3\2\2\2\u012b\u012c\7A\2\2\u012cX\3\2\2\2\u012d\u012e\7B\2\2\u012eZ"+
		"\3\2\2\2\u012f\u0130\7]\2\2\u0130\\\3\2\2\2\u0131\u0132\7_\2\2\u0132^"+
		"\3\2\2\2\u0133\u0134\7^\2\2\u0134`\3\2\2\2\u0135\u0136\7}\2\2\u0136b\3"+
		"\2\2\2\u0137\u0138\7\177\2\2\u0138d\3\2\2\2\u0139\u013a\7`\2\2\u013af"+
		"\3\2\2\2\u013b\u013c\7\u0080\2\2\u013ch\3\2\2\2\u013d\u013e\7~\2\2\u013e"+
		"j\3\2\2\2\u013f\u0140\7a\2\2\u0140l\3\2\2\2\17\2~\u00a5\u00be\u00c4\u00c9"+
		"\u00cb\u00d1\u00da\u00e0\u00e3\u00ed\u00fb\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}