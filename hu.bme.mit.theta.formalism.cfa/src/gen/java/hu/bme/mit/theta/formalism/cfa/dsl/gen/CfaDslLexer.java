// Generated from CfaDsl.g4 by ANTLR 4.5.3
package hu.bme.mit.theta.formalism.cfa.dsl.gen;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class CfaDslLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.5.3", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		VAR=1, MAIN=2, PROCESS=3, INIT=4, FINAL=5, ERROR=6, LOC=7, BOOLTYPE=8, 
		INTTYPE=9, RATTYPE=10, IF=11, THEN=12, ELSE=13, IFF=14, IMPLY=15, FORALL=16, 
		EXISTS=17, OR=18, AND=19, NOT=20, EQ=21, NEQ=22, LT=23, LEQ=24, GT=25, 
		GEQ=26, PLUS=27, MINUS=28, MUL=29, DIV=30, MOD=31, REM=32, PERCENT=33, 
		PRIME=34, TRUE=35, FALSE=36, ASSIGN=37, HAVOC=38, ASSUME=39, RETURN=40, 
		INT=41, NAT=42, SIGN=43, DOT=44, ID=45, UNDERSCORE=46, DIGIT=47, LETTER=48, 
		LPAREN=49, RPAREN=50, LBRACK=51, RBRACK=52, LBRAC=53, RBRAC=54, COMMA=55, 
		COLON=56, SEMICOLON=57, QUOT=58, LARROW=59, RARROW=60, WS=61, COMMENT=62, 
		LINE_COMMENT=63;
	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	public static final String[] ruleNames = {
		"VAR", "MAIN", "PROCESS", "INIT", "FINAL", "ERROR", "LOC", "BOOLTYPE", 
		"INTTYPE", "RATTYPE", "IF", "THEN", "ELSE", "IFF", "IMPLY", "FORALL", 
		"EXISTS", "OR", "AND", "NOT", "EQ", "NEQ", "LT", "LEQ", "GT", "GEQ", "PLUS", 
		"MINUS", "MUL", "DIV", "MOD", "REM", "PERCENT", "PRIME", "TRUE", "FALSE", 
		"ASSIGN", "HAVOC", "ASSUME", "RETURN", "INT", "NAT", "SIGN", "DOT", "ID", 
		"UNDERSCORE", "DIGIT", "LETTER", "LPAREN", "RPAREN", "LBRACK", "RBRACK", 
		"LBRAC", "RBRAC", "COMMA", "COLON", "SEMICOLON", "QUOT", "LARROW", "RARROW", 
		"WS", "COMMENT", "LINE_COMMENT"
	};

	private static final String[] _LITERAL_NAMES = {
		null, "'var'", "'main'", "'process'", "'init'", "'final'", "'error'", 
		"'loc'", "'bool'", "'int'", "'rat'", "'if'", "'then'", "'else'", "'iff'", 
		"'imply'", "'forall'", "'exists'", "'or'", "'and'", "'not'", "'='", "'/='", 
		"'<'", "'<='", "'>'", "'>='", "'+'", "'-'", "'*'", "'/'", "'mod'", "'rem'", 
		"'%'", null, "'true'", "'false'", "':='", "'havoc'", "'assume'", "'return'", 
		null, null, null, "'.'", null, "'_'", null, null, "'('", "')'", "'['", 
		"']'", "'{'", "'}'", "','", "':'", "';'", null, "'<-'", "'->'"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, "VAR", "MAIN", "PROCESS", "INIT", "FINAL", "ERROR", "LOC", "BOOLTYPE", 
		"INTTYPE", "RATTYPE", "IF", "THEN", "ELSE", "IFF", "IMPLY", "FORALL", 
		"EXISTS", "OR", "AND", "NOT", "EQ", "NEQ", "LT", "LEQ", "GT", "GEQ", "PLUS", 
		"MINUS", "MUL", "DIV", "MOD", "REM", "PERCENT", "PRIME", "TRUE", "FALSE", 
		"ASSIGN", "HAVOC", "ASSUME", "RETURN", "INT", "NAT", "SIGN", "DOT", "ID", 
		"UNDERSCORE", "DIGIT", "LETTER", "LPAREN", "RPAREN", "LBRACK", "RBRACK", 
		"LBRAC", "RBRAC", "COMMA", "COLON", "SEMICOLON", "QUOT", "LARROW", "RARROW", 
		"WS", "COMMENT", "LINE_COMMENT"
	};
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


	public CfaDslLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "CfaDsl.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\2A\u0185\b\1\4\2\t"+
		"\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t+\4"+
		",\t,\4-\t-\4.\t.\4/\t/\4\60\t\60\4\61\t\61\4\62\t\62\4\63\t\63\4\64\t"+
		"\64\4\65\t\65\4\66\t\66\4\67\t\67\48\t8\49\t9\4:\t:\4;\t;\4<\t<\4=\t="+
		"\4>\t>\4?\t?\4@\t@\3\2\3\2\3\2\3\2\3\3\3\3\3\3\3\3\3\3\3\4\3\4\3\4\3\4"+
		"\3\4\3\4\3\4\3\4\3\5\3\5\3\5\3\5\3\5\3\6\3\6\3\6\3\6\3\6\3\6\3\7\3\7\3"+
		"\7\3\7\3\7\3\7\3\b\3\b\3\b\3\b\3\t\3\t\3\t\3\t\3\t\3\n\3\n\3\n\3\n\3\13"+
		"\3\13\3\13\3\13\3\f\3\f\3\f\3\r\3\r\3\r\3\r\3\r\3\16\3\16\3\16\3\16\3"+
		"\16\3\17\3\17\3\17\3\17\3\20\3\20\3\20\3\20\3\20\3\20\3\21\3\21\3\21\3"+
		"\21\3\21\3\21\3\21\3\22\3\22\3\22\3\22\3\22\3\22\3\22\3\23\3\23\3\23\3"+
		"\24\3\24\3\24\3\24\3\25\3\25\3\25\3\25\3\26\3\26\3\27\3\27\3\27\3\30\3"+
		"\30\3\31\3\31\3\31\3\32\3\32\3\33\3\33\3\33\3\34\3\34\3\35\3\35\3\36\3"+
		"\36\3\37\3\37\3 \3 \3 \3 \3!\3!\3!\3!\3\"\3\"\3#\3#\3$\3$\3$\3$\3$\3%"+
		"\3%\3%\3%\3%\3%\3&\3&\3&\3\'\3\'\3\'\3\'\3\'\3\'\3(\3(\3(\3(\3(\3(\3("+
		"\3)\3)\3)\3)\3)\3)\3)\3*\5*\u012b\n*\3*\3*\3+\6+\u0130\n+\r+\16+\u0131"+
		"\3,\3,\5,\u0136\n,\3-\3-\3.\3.\5.\u013c\n.\3.\3.\3.\7.\u0141\n.\f.\16"+
		".\u0144\13.\3/\3/\3\60\3\60\3\61\3\61\3\62\3\62\3\63\3\63\3\64\3\64\3"+
		"\65\3\65\3\66\3\66\3\67\3\67\38\38\39\39\3:\3:\3;\3;\3<\3<\3<\3=\3=\3"+
		"=\3>\6>\u0167\n>\r>\16>\u0168\3>\3>\3?\3?\3?\3?\7?\u0171\n?\f?\16?\u0174"+
		"\13?\3?\3?\3?\3?\3?\3@\3@\3@\3@\7@\u017f\n@\f@\16@\u0182\13@\3@\3@\3\u0172"+
		"\2A\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33\17\35"+
		"\20\37\21!\22#\23%\24\'\25)\26+\27-\30/\31\61\32\63\33\65\34\67\359\36"+
		";\37= ?!A\"C#E$G%I&K\'M(O)Q*S+U,W-Y.[/]\60_\61a\62c\63e\64g\65i\66k\67"+
		"m8o9q:s;u<w=y>{?}@\177A\3\2\6\3\2\62;\4\2C\\c|\5\2\13\f\16\17\"\"\4\2"+
		"\f\f\17\17\u018e\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13"+
		"\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2"+
		"\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2"+
		"!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3"+
		"\2\2\2\2/\3\2\2\2\2\61\3\2\2\2\2\63\3\2\2\2\2\65\3\2\2\2\2\67\3\2\2\2"+
		"\29\3\2\2\2\2;\3\2\2\2\2=\3\2\2\2\2?\3\2\2\2\2A\3\2\2\2\2C\3\2\2\2\2E"+
		"\3\2\2\2\2G\3\2\2\2\2I\3\2\2\2\2K\3\2\2\2\2M\3\2\2\2\2O\3\2\2\2\2Q\3\2"+
		"\2\2\2S\3\2\2\2\2U\3\2\2\2\2W\3\2\2\2\2Y\3\2\2\2\2[\3\2\2\2\2]\3\2\2\2"+
		"\2_\3\2\2\2\2a\3\2\2\2\2c\3\2\2\2\2e\3\2\2\2\2g\3\2\2\2\2i\3\2\2\2\2k"+
		"\3\2\2\2\2m\3\2\2\2\2o\3\2\2\2\2q\3\2\2\2\2s\3\2\2\2\2u\3\2\2\2\2w\3\2"+
		"\2\2\2y\3\2\2\2\2{\3\2\2\2\2}\3\2\2\2\2\177\3\2\2\2\3\u0081\3\2\2\2\5"+
		"\u0085\3\2\2\2\7\u008a\3\2\2\2\t\u0092\3\2\2\2\13\u0097\3\2\2\2\r\u009d"+
		"\3\2\2\2\17\u00a3\3\2\2\2\21\u00a7\3\2\2\2\23\u00ac\3\2\2\2\25\u00b0\3"+
		"\2\2\2\27\u00b4\3\2\2\2\31\u00b7\3\2\2\2\33\u00bc\3\2\2\2\35\u00c1\3\2"+
		"\2\2\37\u00c5\3\2\2\2!\u00cb\3\2\2\2#\u00d2\3\2\2\2%\u00d9\3\2\2\2\'\u00dc"+
		"\3\2\2\2)\u00e0\3\2\2\2+\u00e4\3\2\2\2-\u00e6\3\2\2\2/\u00e9\3\2\2\2\61"+
		"\u00eb\3\2\2\2\63\u00ee\3\2\2\2\65\u00f0\3\2\2\2\67\u00f3\3\2\2\29\u00f5"+
		"\3\2\2\2;\u00f7\3\2\2\2=\u00f9\3\2\2\2?\u00fb\3\2\2\2A\u00ff\3\2\2\2C"+
		"\u0103\3\2\2\2E\u0105\3\2\2\2G\u0107\3\2\2\2I\u010c\3\2\2\2K\u0112\3\2"+
		"\2\2M\u0115\3\2\2\2O\u011b\3\2\2\2Q\u0122\3\2\2\2S\u012a\3\2\2\2U\u012f"+
		"\3\2\2\2W\u0135\3\2\2\2Y\u0137\3\2\2\2[\u013b\3\2\2\2]\u0145\3\2\2\2_"+
		"\u0147\3\2\2\2a\u0149\3\2\2\2c\u014b\3\2\2\2e\u014d\3\2\2\2g\u014f\3\2"+
		"\2\2i\u0151\3\2\2\2k\u0153\3\2\2\2m\u0155\3\2\2\2o\u0157\3\2\2\2q\u0159"+
		"\3\2\2\2s\u015b\3\2\2\2u\u015d\3\2\2\2w\u015f\3\2\2\2y\u0162\3\2\2\2{"+
		"\u0166\3\2\2\2}\u016c\3\2\2\2\177\u017a\3\2\2\2\u0081\u0082\7x\2\2\u0082"+
		"\u0083\7c\2\2\u0083\u0084\7t\2\2\u0084\4\3\2\2\2\u0085\u0086\7o\2\2\u0086"+
		"\u0087\7c\2\2\u0087\u0088\7k\2\2\u0088\u0089\7p\2\2\u0089\6\3\2\2\2\u008a"+
		"\u008b\7r\2\2\u008b\u008c\7t\2\2\u008c\u008d\7q\2\2\u008d\u008e\7e\2\2"+
		"\u008e\u008f\7g\2\2\u008f\u0090\7u\2\2\u0090\u0091\7u\2\2\u0091\b\3\2"+
		"\2\2\u0092\u0093\7k\2\2\u0093\u0094\7p\2\2\u0094\u0095\7k\2\2\u0095\u0096"+
		"\7v\2\2\u0096\n\3\2\2\2\u0097\u0098\7h\2\2\u0098\u0099\7k\2\2\u0099\u009a"+
		"\7p\2\2\u009a\u009b\7c\2\2\u009b\u009c\7n\2\2\u009c\f\3\2\2\2\u009d\u009e"+
		"\7g\2\2\u009e\u009f\7t\2\2\u009f\u00a0\7t\2\2\u00a0\u00a1\7q\2\2\u00a1"+
		"\u00a2\7t\2\2\u00a2\16\3\2\2\2\u00a3\u00a4\7n\2\2\u00a4\u00a5\7q\2\2\u00a5"+
		"\u00a6\7e\2\2\u00a6\20\3\2\2\2\u00a7\u00a8\7d\2\2\u00a8\u00a9\7q\2\2\u00a9"+
		"\u00aa\7q\2\2\u00aa\u00ab\7n\2\2\u00ab\22\3\2\2\2\u00ac\u00ad\7k\2\2\u00ad"+
		"\u00ae\7p\2\2\u00ae\u00af\7v\2\2\u00af\24\3\2\2\2\u00b0\u00b1\7t\2\2\u00b1"+
		"\u00b2\7c\2\2\u00b2\u00b3\7v\2\2\u00b3\26\3\2\2\2\u00b4\u00b5\7k\2\2\u00b5"+
		"\u00b6\7h\2\2\u00b6\30\3\2\2\2\u00b7\u00b8\7v\2\2\u00b8\u00b9\7j\2\2\u00b9"+
		"\u00ba\7g\2\2\u00ba\u00bb\7p\2\2\u00bb\32\3\2\2\2\u00bc\u00bd\7g\2\2\u00bd"+
		"\u00be\7n\2\2\u00be\u00bf\7u\2\2\u00bf\u00c0\7g\2\2\u00c0\34\3\2\2\2\u00c1"+
		"\u00c2\7k\2\2\u00c2\u00c3\7h\2\2\u00c3\u00c4\7h\2\2\u00c4\36\3\2\2\2\u00c5"+
		"\u00c6\7k\2\2\u00c6\u00c7\7o\2\2\u00c7\u00c8\7r\2\2\u00c8\u00c9\7n\2\2"+
		"\u00c9\u00ca\7{\2\2\u00ca \3\2\2\2\u00cb\u00cc\7h\2\2\u00cc\u00cd\7q\2"+
		"\2\u00cd\u00ce\7t\2\2\u00ce\u00cf\7c\2\2\u00cf\u00d0\7n\2\2\u00d0\u00d1"+
		"\7n\2\2\u00d1\"\3\2\2\2\u00d2\u00d3\7g\2\2\u00d3\u00d4\7z\2\2\u00d4\u00d5"+
		"\7k\2\2\u00d5\u00d6\7u\2\2\u00d6\u00d7\7v\2\2\u00d7\u00d8\7u\2\2\u00d8"+
		"$\3\2\2\2\u00d9\u00da\7q\2\2\u00da\u00db\7t\2\2\u00db&\3\2\2\2\u00dc\u00dd"+
		"\7c\2\2\u00dd\u00de\7p\2\2\u00de\u00df\7f\2\2\u00df(\3\2\2\2\u00e0\u00e1"+
		"\7p\2\2\u00e1\u00e2\7q\2\2\u00e2\u00e3\7v\2\2\u00e3*\3\2\2\2\u00e4\u00e5"+
		"\7?\2\2\u00e5,\3\2\2\2\u00e6\u00e7\7\61\2\2\u00e7\u00e8\7?\2\2\u00e8."+
		"\3\2\2\2\u00e9\u00ea\7>\2\2\u00ea\60\3\2\2\2\u00eb\u00ec\7>\2\2\u00ec"+
		"\u00ed\7?\2\2\u00ed\62\3\2\2\2\u00ee\u00ef\7@\2\2\u00ef\64\3\2\2\2\u00f0"+
		"\u00f1\7@\2\2\u00f1\u00f2\7?\2\2\u00f2\66\3\2\2\2\u00f3\u00f4\7-\2\2\u00f4"+
		"8\3\2\2\2\u00f5\u00f6\7/\2\2\u00f6:\3\2\2\2\u00f7\u00f8\7,\2\2\u00f8<"+
		"\3\2\2\2\u00f9\u00fa\7\61\2\2\u00fa>\3\2\2\2\u00fb\u00fc\7o\2\2\u00fc"+
		"\u00fd\7q\2\2\u00fd\u00fe\7f\2\2\u00fe@\3\2\2\2\u00ff\u0100\7t\2\2\u0100"+
		"\u0101\7g\2\2\u0101\u0102\7o\2\2\u0102B\3\2\2\2\u0103\u0104\7\'\2\2\u0104"+
		"D\3\2\2\2\u0105\u0106\7)\2\2\u0106F\3\2\2\2\u0107\u0108\7v\2\2\u0108\u0109"+
		"\7t\2\2\u0109\u010a\7w\2\2\u010a\u010b\7g\2\2\u010bH\3\2\2\2\u010c\u010d"+
		"\7h\2\2\u010d\u010e\7c\2\2\u010e\u010f\7n\2\2\u010f\u0110\7u\2\2\u0110"+
		"\u0111\7g\2\2\u0111J\3\2\2\2\u0112\u0113\7<\2\2\u0113\u0114\7?\2\2\u0114"+
		"L\3\2\2\2\u0115\u0116\7j\2\2\u0116\u0117\7c\2\2\u0117\u0118\7x\2\2\u0118"+
		"\u0119\7q\2\2\u0119\u011a\7e\2\2\u011aN\3\2\2\2\u011b\u011c\7c\2\2\u011c"+
		"\u011d\7u\2\2\u011d\u011e\7u\2\2\u011e\u011f\7w\2\2\u011f\u0120\7o\2\2"+
		"\u0120\u0121\7g\2\2\u0121P\3\2\2\2\u0122\u0123\7t\2\2\u0123\u0124\7g\2"+
		"\2\u0124\u0125\7v\2\2\u0125\u0126\7w\2\2\u0126\u0127\7t\2\2\u0127\u0128"+
		"\7p\2\2\u0128R\3\2\2\2\u0129\u012b\5W,\2\u012a\u0129\3\2\2\2\u012a\u012b"+
		"\3\2\2\2\u012b\u012c\3\2\2\2\u012c\u012d\5U+\2\u012dT\3\2\2\2\u012e\u0130"+
		"\5_\60\2\u012f\u012e\3\2\2\2\u0130\u0131\3\2\2\2\u0131\u012f\3\2\2\2\u0131"+
		"\u0132\3\2\2\2\u0132V\3\2\2\2\u0133\u0136\5\67\34\2\u0134\u0136\59\35"+
		"\2\u0135\u0133\3\2\2\2\u0135\u0134\3\2\2\2\u0136X\3\2\2\2\u0137\u0138"+
		"\7\60\2\2\u0138Z\3\2\2\2\u0139\u013c\5a\61\2\u013a\u013c\5]/\2\u013b\u0139"+
		"\3\2\2\2\u013b\u013a\3\2\2\2\u013c\u0142\3\2\2\2\u013d\u0141\5a\61\2\u013e"+
		"\u0141\5]/\2\u013f\u0141\5_\60\2\u0140\u013d\3\2\2\2\u0140\u013e\3\2\2"+
		"\2\u0140\u013f\3\2\2\2\u0141\u0144\3\2\2\2\u0142\u0140\3\2\2\2\u0142\u0143"+
		"\3\2\2\2\u0143\\\3\2\2\2\u0144\u0142\3\2\2\2\u0145\u0146\7a\2\2\u0146"+
		"^\3\2\2\2\u0147\u0148\t\2\2\2\u0148`\3\2\2\2\u0149\u014a\t\3\2\2\u014a"+
		"b\3\2\2\2\u014b\u014c\7*\2\2\u014cd\3\2\2\2\u014d\u014e\7+\2\2\u014ef"+
		"\3\2\2\2\u014f\u0150\7]\2\2\u0150h\3\2\2\2\u0151\u0152\7_\2\2\u0152j\3"+
		"\2\2\2\u0153\u0154\7}\2\2\u0154l\3\2\2\2\u0155\u0156\7\177\2\2\u0156n"+
		"\3\2\2\2\u0157\u0158\7.\2\2\u0158p\3\2\2\2\u0159\u015a\7<\2\2\u015ar\3"+
		"\2\2\2\u015b\u015c\7=\2\2\u015ct\3\2\2\2\u015d\u015e\7)\2\2\u015ev\3\2"+
		"\2\2\u015f\u0160\7>\2\2\u0160\u0161\7/\2\2\u0161x\3\2\2\2\u0162\u0163"+
		"\7/\2\2\u0163\u0164\7@\2\2\u0164z\3\2\2\2\u0165\u0167\t\4\2\2\u0166\u0165"+
		"\3\2\2\2\u0167\u0168\3\2\2\2\u0168\u0166\3\2\2\2\u0168\u0169\3\2\2\2\u0169"+
		"\u016a\3\2\2\2\u016a\u016b\b>\2\2\u016b|\3\2\2\2\u016c\u016d\7\61\2\2"+
		"\u016d\u016e\7,\2\2\u016e\u0172\3\2\2\2\u016f\u0171\13\2\2\2\u0170\u016f"+
		"\3\2\2\2\u0171\u0174\3\2\2\2\u0172\u0173\3\2\2\2\u0172\u0170\3\2\2\2\u0173"+
		"\u0175\3\2\2\2\u0174\u0172\3\2\2\2\u0175\u0176\7,\2\2\u0176\u0177\7\61"+
		"\2\2\u0177\u0178\3\2\2\2\u0178\u0179\b?\2\2\u0179~\3\2\2\2\u017a\u017b"+
		"\7\61\2\2\u017b\u017c\7\61\2\2\u017c\u0180\3\2\2\2\u017d\u017f\n\5\2\2"+
		"\u017e\u017d\3\2\2\2\u017f\u0182\3\2\2\2\u0180\u017e\3\2\2\2\u0180\u0181"+
		"\3\2\2\2\u0181\u0183\3\2\2\2\u0182\u0180\3\2\2\2\u0183\u0184\b@\2\2\u0184"+
		"\u0080\3\2\2\2\f\2\u012a\u0131\u0135\u013b\u0140\u0142\u0168\u0172\u0180"+
		"\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}