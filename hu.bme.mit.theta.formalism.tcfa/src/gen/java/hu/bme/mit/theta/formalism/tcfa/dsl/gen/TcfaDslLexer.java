// Generated from TcfaDsl.g4 by ANTLR 4.5.3
package hu.bme.mit.theta.formalism.tcfa.dsl.gen;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class TcfaDslLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.5.3", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		SPEC=1, CONST=2, VAR=3, REF=4, VAL=5, AUTOMATON=6, URGENT=7, INIT=8, LOC=9, 
		DBAR=10, BOOLTYPE=11, INTTYPE=12, RATTYPE=13, CLOCKTYPE=14, IF=15, THEN=16, 
		ELSE=17, IFF=18, IMPLY=19, FORALL=20, EXISTS=21, OR=22, AND=23, NOT=24, 
		EQ=25, NEQ=26, LT=27, LEQ=28, GT=29, GEQ=30, PLUS=31, MINUS=32, MUL=33, 
		RDIV=34, IDIV=35, MOD=36, REM=37, PERCENT=38, TRUE=39, FALSE=40, ASSIGN=41, 
		HAVOC=42, ASSUME=43, INT=44, NAT=45, SIGN=46, DOT=47, ID=48, UNDERSCORE=49, 
		DIGIT=50, LETTER=51, LPAREN=52, RPAREN=53, LBRACK=54, RBRACK=55, LBRAC=56, 
		RBRAC=57, COMMA=58, COLON=59, SEMICOLON=60, QUOT=61, LARROW=62, RARROW=63, 
		WS=64, COMMENT=65, LINE_COMMENT=66;
	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	public static final String[] ruleNames = {
		"SPEC", "CONST", "VAR", "REF", "VAL", "AUTOMATON", "URGENT", "INIT", "LOC", 
		"DBAR", "BOOLTYPE", "INTTYPE", "RATTYPE", "CLOCKTYPE", "IF", "THEN", "ELSE", 
		"IFF", "IMPLY", "FORALL", "EXISTS", "OR", "AND", "NOT", "EQ", "NEQ", "LT", 
		"LEQ", "GT", "GEQ", "PLUS", "MINUS", "MUL", "RDIV", "IDIV", "MOD", "REM", 
		"PERCENT", "TRUE", "FALSE", "ASSIGN", "HAVOC", "ASSUME", "INT", "NAT", 
		"SIGN", "DOT", "ID", "UNDERSCORE", "DIGIT", "LETTER", "LPAREN", "RPAREN", 
		"LBRACK", "RBRACK", "LBRAC", "RBRAC", "COMMA", "COLON", "SEMICOLON", "QUOT", 
		"LARROW", "RARROW", "WS", "COMMENT", "LINE_COMMENT"
	};

	private static final String[] _LITERAL_NAMES = {
		null, "'specification'", "'const'", "'var'", "'ref'", "'val'", "'automaton'", 
		"'urgent'", "'init'", "'loc'", "'||'", "'bool'", "'int'", "'rat'", "'clock'", 
		"'if'", "'then'", "'else'", "'iff'", "'imply'", "'forall'", "'exists'", 
		"'or'", "'and'", "'not'", "'='", "'/='", "'<'", "'<='", "'>'", "'>='", 
		"'+'", "'-'", "'*'", "'/'", "'div'", "'mod'", "'rem'", "'%'", "'true'", 
		"'false'", "':='", "'havoc'", "'assume'", null, null, null, "'.'", null, 
		"'_'", null, null, "'('", "')'", "'['", "']'", "'{'", "'}'", "','", "':'", 
		"';'", "'''", "'<-'", "'->'"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, "SPEC", "CONST", "VAR", "REF", "VAL", "AUTOMATON", "URGENT", "INIT", 
		"LOC", "DBAR", "BOOLTYPE", "INTTYPE", "RATTYPE", "CLOCKTYPE", "IF", "THEN", 
		"ELSE", "IFF", "IMPLY", "FORALL", "EXISTS", "OR", "AND", "NOT", "EQ", 
		"NEQ", "LT", "LEQ", "GT", "GEQ", "PLUS", "MINUS", "MUL", "RDIV", "IDIV", 
		"MOD", "REM", "PERCENT", "TRUE", "FALSE", "ASSIGN", "HAVOC", "ASSUME", 
		"INT", "NAT", "SIGN", "DOT", "ID", "UNDERSCORE", "DIGIT", "LETTER", "LPAREN", 
		"RPAREN", "LBRACK", "RBRACK", "LBRAC", "RBRAC", "COMMA", "COLON", "SEMICOLON", 
		"QUOT", "LARROW", "RARROW", "WS", "COMMENT", "LINE_COMMENT"
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


	public TcfaDslLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "TcfaDsl.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\2D\u01a3\b\1\4\2\t"+
		"\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t+\4"+
		",\t,\4-\t-\4.\t.\4/\t/\4\60\t\60\4\61\t\61\4\62\t\62\4\63\t\63\4\64\t"+
		"\64\4\65\t\65\4\66\t\66\4\67\t\67\48\t8\49\t9\4:\t:\4;\t;\4<\t<\4=\t="+
		"\4>\t>\4?\t?\4@\t@\4A\tA\4B\tB\4C\tC\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3"+
		"\2\3\2\3\2\3\2\3\2\3\2\3\3\3\3\3\3\3\3\3\3\3\3\3\4\3\4\3\4\3\4\3\5\3\5"+
		"\3\5\3\5\3\6\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3\7\3\7\3\7\3\7\3\7\3\7\3\b\3"+
		"\b\3\b\3\b\3\b\3\b\3\b\3\t\3\t\3\t\3\t\3\t\3\n\3\n\3\n\3\n\3\13\3\13\3"+
		"\13\3\f\3\f\3\f\3\f\3\f\3\r\3\r\3\r\3\r\3\16\3\16\3\16\3\16\3\17\3\17"+
		"\3\17\3\17\3\17\3\17\3\20\3\20\3\20\3\21\3\21\3\21\3\21\3\21\3\22\3\22"+
		"\3\22\3\22\3\22\3\23\3\23\3\23\3\23\3\24\3\24\3\24\3\24\3\24\3\24\3\25"+
		"\3\25\3\25\3\25\3\25\3\25\3\25\3\26\3\26\3\26\3\26\3\26\3\26\3\26\3\27"+
		"\3\27\3\27\3\30\3\30\3\30\3\30\3\31\3\31\3\31\3\31\3\32\3\32\3\33\3\33"+
		"\3\33\3\34\3\34\3\35\3\35\3\35\3\36\3\36\3\37\3\37\3\37\3 \3 \3!\3!\3"+
		"\"\3\"\3#\3#\3$\3$\3$\3$\3%\3%\3%\3%\3&\3&\3&\3&\3\'\3\'\3(\3(\3(\3(\3"+
		"(\3)\3)\3)\3)\3)\3)\3*\3*\3*\3+\3+\3+\3+\3+\3+\3,\3,\3,\3,\3,\3,\3,\3"+
		"-\5-\u0149\n-\3-\3-\3.\6.\u014e\n.\r.\16.\u014f\3/\3/\5/\u0154\n/\3\60"+
		"\3\60\3\61\3\61\5\61\u015a\n\61\3\61\3\61\3\61\7\61\u015f\n\61\f\61\16"+
		"\61\u0162\13\61\3\62\3\62\3\63\3\63\3\64\3\64\3\65\3\65\3\66\3\66\3\67"+
		"\3\67\38\38\39\39\3:\3:\3;\3;\3<\3<\3=\3=\3>\3>\3?\3?\3?\3@\3@\3@\3A\6"+
		"A\u0185\nA\rA\16A\u0186\3A\3A\3B\3B\3B\3B\7B\u018f\nB\fB\16B\u0192\13"+
		"B\3B\3B\3B\3B\3B\3C\3C\3C\3C\7C\u019d\nC\fC\16C\u01a0\13C\3C\3C\3\u0190"+
		"\2D\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33\17\35"+
		"\20\37\21!\22#\23%\24\'\25)\26+\27-\30/\31\61\32\63\33\65\34\67\359\36"+
		";\37= ?!A\"C#E$G%I&K\'M(O)Q*S+U,W-Y.[/]\60_\61a\62c\63e\64g\65i\66k\67"+
		"m8o9q:s;u<w=y>{?}@\177A\u0081B\u0083C\u0085D\3\2\6\3\2\62;\4\2C\\c|\5"+
		"\2\13\f\16\17\"\"\4\2\f\f\17\17\u01ac\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2"+
		"\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2"+
		"\23\3\2\2\2\2\25\3\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3"+
		"\2\2\2\2\37\3\2\2\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3"+
		"\2\2\2\2+\3\2\2\2\2-\3\2\2\2\2/\3\2\2\2\2\61\3\2\2\2\2\63\3\2\2\2\2\65"+
		"\3\2\2\2\2\67\3\2\2\2\29\3\2\2\2\2;\3\2\2\2\2=\3\2\2\2\2?\3\2\2\2\2A\3"+
		"\2\2\2\2C\3\2\2\2\2E\3\2\2\2\2G\3\2\2\2\2I\3\2\2\2\2K\3\2\2\2\2M\3\2\2"+
		"\2\2O\3\2\2\2\2Q\3\2\2\2\2S\3\2\2\2\2U\3\2\2\2\2W\3\2\2\2\2Y\3\2\2\2\2"+
		"[\3\2\2\2\2]\3\2\2\2\2_\3\2\2\2\2a\3\2\2\2\2c\3\2\2\2\2e\3\2\2\2\2g\3"+
		"\2\2\2\2i\3\2\2\2\2k\3\2\2\2\2m\3\2\2\2\2o\3\2\2\2\2q\3\2\2\2\2s\3\2\2"+
		"\2\2u\3\2\2\2\2w\3\2\2\2\2y\3\2\2\2\2{\3\2\2\2\2}\3\2\2\2\2\177\3\2\2"+
		"\2\2\u0081\3\2\2\2\2\u0083\3\2\2\2\2\u0085\3\2\2\2\3\u0087\3\2\2\2\5\u0095"+
		"\3\2\2\2\7\u009b\3\2\2\2\t\u009f\3\2\2\2\13\u00a3\3\2\2\2\r\u00a7\3\2"+
		"\2\2\17\u00b1\3\2\2\2\21\u00b8\3\2\2\2\23\u00bd\3\2\2\2\25\u00c1\3\2\2"+
		"\2\27\u00c4\3\2\2\2\31\u00c9\3\2\2\2\33\u00cd\3\2\2\2\35\u00d1\3\2\2\2"+
		"\37\u00d7\3\2\2\2!\u00da\3\2\2\2#\u00df\3\2\2\2%\u00e4\3\2\2\2\'\u00e8"+
		"\3\2\2\2)\u00ee\3\2\2\2+\u00f5\3\2\2\2-\u00fc\3\2\2\2/\u00ff\3\2\2\2\61"+
		"\u0103\3\2\2\2\63\u0107\3\2\2\2\65\u0109\3\2\2\2\67\u010c\3\2\2\29\u010e"+
		"\3\2\2\2;\u0111\3\2\2\2=\u0113\3\2\2\2?\u0116\3\2\2\2A\u0118\3\2\2\2C"+
		"\u011a\3\2\2\2E\u011c\3\2\2\2G\u011e\3\2\2\2I\u0122\3\2\2\2K\u0126\3\2"+
		"\2\2M\u012a\3\2\2\2O\u012c\3\2\2\2Q\u0131\3\2\2\2S\u0137\3\2\2\2U\u013a"+
		"\3\2\2\2W\u0140\3\2\2\2Y\u0148\3\2\2\2[\u014d\3\2\2\2]\u0153\3\2\2\2_"+
		"\u0155\3\2\2\2a\u0159\3\2\2\2c\u0163\3\2\2\2e\u0165\3\2\2\2g\u0167\3\2"+
		"\2\2i\u0169\3\2\2\2k\u016b\3\2\2\2m\u016d\3\2\2\2o\u016f\3\2\2\2q\u0171"+
		"\3\2\2\2s\u0173\3\2\2\2u\u0175\3\2\2\2w\u0177\3\2\2\2y\u0179\3\2\2\2{"+
		"\u017b\3\2\2\2}\u017d\3\2\2\2\177\u0180\3\2\2\2\u0081\u0184\3\2\2\2\u0083"+
		"\u018a\3\2\2\2\u0085\u0198\3\2\2\2\u0087\u0088\7u\2\2\u0088\u0089\7r\2"+
		"\2\u0089\u008a\7g\2\2\u008a\u008b\7e\2\2\u008b\u008c\7k\2\2\u008c\u008d"+
		"\7h\2\2\u008d\u008e\7k\2\2\u008e\u008f\7e\2\2\u008f\u0090\7c\2\2\u0090"+
		"\u0091\7v\2\2\u0091\u0092\7k\2\2\u0092\u0093\7q\2\2\u0093\u0094\7p\2\2"+
		"\u0094\4\3\2\2\2\u0095\u0096\7e\2\2\u0096\u0097\7q\2\2\u0097\u0098\7p"+
		"\2\2\u0098\u0099\7u\2\2\u0099\u009a\7v\2\2\u009a\6\3\2\2\2\u009b\u009c"+
		"\7x\2\2\u009c\u009d\7c\2\2\u009d\u009e\7t\2\2\u009e\b\3\2\2\2\u009f\u00a0"+
		"\7t\2\2\u00a0\u00a1\7g\2\2\u00a1\u00a2\7h\2\2\u00a2\n\3\2\2\2\u00a3\u00a4"+
		"\7x\2\2\u00a4\u00a5\7c\2\2\u00a5\u00a6\7n\2\2\u00a6\f\3\2\2\2\u00a7\u00a8"+
		"\7c\2\2\u00a8\u00a9\7w\2\2\u00a9\u00aa\7v\2\2\u00aa\u00ab\7q\2\2\u00ab"+
		"\u00ac\7o\2\2\u00ac\u00ad\7c\2\2\u00ad\u00ae\7v\2\2\u00ae\u00af\7q\2\2"+
		"\u00af\u00b0\7p\2\2\u00b0\16\3\2\2\2\u00b1\u00b2\7w\2\2\u00b2\u00b3\7"+
		"t\2\2\u00b3\u00b4\7i\2\2\u00b4\u00b5\7g\2\2\u00b5\u00b6\7p\2\2\u00b6\u00b7"+
		"\7v\2\2\u00b7\20\3\2\2\2\u00b8\u00b9\7k\2\2\u00b9\u00ba\7p\2\2\u00ba\u00bb"+
		"\7k\2\2\u00bb\u00bc\7v\2\2\u00bc\22\3\2\2\2\u00bd\u00be\7n\2\2\u00be\u00bf"+
		"\7q\2\2\u00bf\u00c0\7e\2\2\u00c0\24\3\2\2\2\u00c1\u00c2\7~\2\2\u00c2\u00c3"+
		"\7~\2\2\u00c3\26\3\2\2\2\u00c4\u00c5\7d\2\2\u00c5\u00c6\7q\2\2\u00c6\u00c7"+
		"\7q\2\2\u00c7\u00c8\7n\2\2\u00c8\30\3\2\2\2\u00c9\u00ca\7k\2\2\u00ca\u00cb"+
		"\7p\2\2\u00cb\u00cc\7v\2\2\u00cc\32\3\2\2\2\u00cd\u00ce\7t\2\2\u00ce\u00cf"+
		"\7c\2\2\u00cf\u00d0\7v\2\2\u00d0\34\3\2\2\2\u00d1\u00d2\7e\2\2\u00d2\u00d3"+
		"\7n\2\2\u00d3\u00d4\7q\2\2\u00d4\u00d5\7e\2\2\u00d5\u00d6\7m\2\2\u00d6"+
		"\36\3\2\2\2\u00d7\u00d8\7k\2\2\u00d8\u00d9\7h\2\2\u00d9 \3\2\2\2\u00da"+
		"\u00db\7v\2\2\u00db\u00dc\7j\2\2\u00dc\u00dd\7g\2\2\u00dd\u00de\7p\2\2"+
		"\u00de\"\3\2\2\2\u00df\u00e0\7g\2\2\u00e0\u00e1\7n\2\2\u00e1\u00e2\7u"+
		"\2\2\u00e2\u00e3\7g\2\2\u00e3$\3\2\2\2\u00e4\u00e5\7k\2\2\u00e5\u00e6"+
		"\7h\2\2\u00e6\u00e7\7h\2\2\u00e7&\3\2\2\2\u00e8\u00e9\7k\2\2\u00e9\u00ea"+
		"\7o\2\2\u00ea\u00eb\7r\2\2\u00eb\u00ec\7n\2\2\u00ec\u00ed\7{\2\2\u00ed"+
		"(\3\2\2\2\u00ee\u00ef\7h\2\2\u00ef\u00f0\7q\2\2\u00f0\u00f1\7t\2\2\u00f1"+
		"\u00f2\7c\2\2\u00f2\u00f3\7n\2\2\u00f3\u00f4\7n\2\2\u00f4*\3\2\2\2\u00f5"+
		"\u00f6\7g\2\2\u00f6\u00f7\7z\2\2\u00f7\u00f8\7k\2\2\u00f8\u00f9\7u\2\2"+
		"\u00f9\u00fa\7v\2\2\u00fa\u00fb\7u\2\2\u00fb,\3\2\2\2\u00fc\u00fd\7q\2"+
		"\2\u00fd\u00fe\7t\2\2\u00fe.\3\2\2\2\u00ff\u0100\7c\2\2\u0100\u0101\7"+
		"p\2\2\u0101\u0102\7f\2\2\u0102\60\3\2\2\2\u0103\u0104\7p\2\2\u0104\u0105"+
		"\7q\2\2\u0105\u0106\7v\2\2\u0106\62\3\2\2\2\u0107\u0108\7?\2\2\u0108\64"+
		"\3\2\2\2\u0109\u010a\7\61\2\2\u010a\u010b\7?\2\2\u010b\66\3\2\2\2\u010c"+
		"\u010d\7>\2\2\u010d8\3\2\2\2\u010e\u010f\7>\2\2\u010f\u0110\7?\2\2\u0110"+
		":\3\2\2\2\u0111\u0112\7@\2\2\u0112<\3\2\2\2\u0113\u0114\7@\2\2\u0114\u0115"+
		"\7?\2\2\u0115>\3\2\2\2\u0116\u0117\7-\2\2\u0117@\3\2\2\2\u0118\u0119\7"+
		"/\2\2\u0119B\3\2\2\2\u011a\u011b\7,\2\2\u011bD\3\2\2\2\u011c\u011d\7\61"+
		"\2\2\u011dF\3\2\2\2\u011e\u011f\7f\2\2\u011f\u0120\7k\2\2\u0120\u0121"+
		"\7x\2\2\u0121H\3\2\2\2\u0122\u0123\7o\2\2\u0123\u0124\7q\2\2\u0124\u0125"+
		"\7f\2\2\u0125J\3\2\2\2\u0126\u0127\7t\2\2\u0127\u0128\7g\2\2\u0128\u0129"+
		"\7o\2\2\u0129L\3\2\2\2\u012a\u012b\7\'\2\2\u012bN\3\2\2\2\u012c\u012d"+
		"\7v\2\2\u012d\u012e\7t\2\2\u012e\u012f\7w\2\2\u012f\u0130\7g\2\2\u0130"+
		"P\3\2\2\2\u0131\u0132\7h\2\2\u0132\u0133\7c\2\2\u0133\u0134\7n\2\2\u0134"+
		"\u0135\7u\2\2\u0135\u0136\7g\2\2\u0136R\3\2\2\2\u0137\u0138\7<\2\2\u0138"+
		"\u0139\7?\2\2\u0139T\3\2\2\2\u013a\u013b\7j\2\2\u013b\u013c\7c\2\2\u013c"+
		"\u013d\7x\2\2\u013d\u013e\7q\2\2\u013e\u013f\7e\2\2\u013fV\3\2\2\2\u0140"+
		"\u0141\7c\2\2\u0141\u0142\7u\2\2\u0142\u0143\7u\2\2\u0143\u0144\7w\2\2"+
		"\u0144\u0145\7o\2\2\u0145\u0146\7g\2\2\u0146X\3\2\2\2\u0147\u0149\5]/"+
		"\2\u0148\u0147\3\2\2\2\u0148\u0149\3\2\2\2\u0149\u014a\3\2\2\2\u014a\u014b"+
		"\5[.\2\u014bZ\3\2\2\2\u014c\u014e\5e\63\2\u014d\u014c\3\2\2\2\u014e\u014f"+
		"\3\2\2\2\u014f\u014d\3\2\2\2\u014f\u0150\3\2\2\2\u0150\\\3\2\2\2\u0151"+
		"\u0154\5? \2\u0152\u0154\5A!\2\u0153\u0151\3\2\2\2\u0153\u0152\3\2\2\2"+
		"\u0154^\3\2\2\2\u0155\u0156\7\60\2\2\u0156`\3\2\2\2\u0157\u015a\5g\64"+
		"\2\u0158\u015a\5c\62\2\u0159\u0157\3\2\2\2\u0159\u0158\3\2\2\2\u015a\u0160"+
		"\3\2\2\2\u015b\u015f\5g\64\2\u015c\u015f\5c\62\2\u015d\u015f\5e\63\2\u015e"+
		"\u015b\3\2\2\2\u015e\u015c\3\2\2\2\u015e\u015d\3\2\2\2\u015f\u0162\3\2"+
		"\2\2\u0160\u015e\3\2\2\2\u0160\u0161\3\2\2\2\u0161b\3\2\2\2\u0162\u0160"+
		"\3\2\2\2\u0163\u0164\7a\2\2\u0164d\3\2\2\2\u0165\u0166\t\2\2\2\u0166f"+
		"\3\2\2\2\u0167\u0168\t\3\2\2\u0168h\3\2\2\2\u0169\u016a\7*\2\2\u016aj"+
		"\3\2\2\2\u016b\u016c\7+\2\2\u016cl\3\2\2\2\u016d\u016e\7]\2\2\u016en\3"+
		"\2\2\2\u016f\u0170\7_\2\2\u0170p\3\2\2\2\u0171\u0172\7}\2\2\u0172r\3\2"+
		"\2\2\u0173\u0174\7\177\2\2\u0174t\3\2\2\2\u0175\u0176\7.\2\2\u0176v\3"+
		"\2\2\2\u0177\u0178\7<\2\2\u0178x\3\2\2\2\u0179\u017a\7=\2\2\u017az\3\2"+
		"\2\2\u017b\u017c\7)\2\2\u017c|\3\2\2\2\u017d\u017e\7>\2\2\u017e\u017f"+
		"\7/\2\2\u017f~\3\2\2\2\u0180\u0181\7/\2\2\u0181\u0182\7@\2\2\u0182\u0080"+
		"\3\2\2\2\u0183\u0185\t\4\2\2\u0184\u0183\3\2\2\2\u0185\u0186\3\2\2\2\u0186"+
		"\u0184\3\2\2\2\u0186\u0187\3\2\2\2\u0187\u0188\3\2\2\2\u0188\u0189\bA"+
		"\2\2\u0189\u0082\3\2\2\2\u018a\u018b\7\61\2\2\u018b\u018c\7,\2\2\u018c"+
		"\u0190\3\2\2\2\u018d\u018f\13\2\2\2\u018e\u018d\3\2\2\2\u018f\u0192\3"+
		"\2\2\2\u0190\u0191\3\2\2\2\u0190\u018e\3\2\2\2\u0191\u0193\3\2\2\2\u0192"+
		"\u0190\3\2\2\2\u0193\u0194\7,\2\2\u0194\u0195\7\61\2\2\u0195\u0196\3\2"+
		"\2\2\u0196\u0197\bB\2\2\u0197\u0084\3\2\2\2\u0198\u0199\7\61\2\2\u0199"+
		"\u019a\7\61\2\2\u019a\u019e\3\2\2\2\u019b\u019d\n\5\2\2\u019c\u019b\3"+
		"\2\2\2\u019d\u01a0\3\2\2\2\u019e\u019c\3\2\2\2\u019e\u019f\3\2\2\2\u019f"+
		"\u01a1\3\2\2\2\u01a0\u019e\3\2\2\2\u01a1\u01a2\bC\2\2\u01a2\u0086\3\2"+
		"\2\2\f\2\u0148\u014f\u0153\u0159\u015e\u0160\u0186\u0190\u019e\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}