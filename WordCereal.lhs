WordCereal: An English passphrase word list


Introduction
============

Recently I went through a personal security audit -- changing passwords,
checking up on 2FA settings, that kind of thing. And I got to thinking about
passphrases. Recall, these are strings of random *words* used as a password,
rather than just strings of random *characters*.

Several word lists have been constructed for the purpose of building passphrases
or otherwise encoding bits as words, including the following.

1. [S/KEY](https://tools.ietf.org/html/rfc1760), which includes a word list.
2. [Diceware](http://world.std.com/~reinhold/diceware.html), designed for use
   with six-sided dice. ([wiki](https://en.wikipedia.org/wiki/Diceware))
3. The [PGP Word List](http://www.mathcs.duq.edu/~juola/papers.d/icslp96.pdf),
   which is intended for encoding any bits, but could be used for passphrases.
   Designed to maximize "phonetic distinctiveness".
   ([wiki](https://en.wikipedia.org/wiki/PGP_word_list))
4. Several word lists by Joseph Bonneau at the
   [EFF](https://www.eff.org/deeplinks/2016/07/new-wordlists-random-passphrases)
   which improve on Diceware in several ways. Notably, code words are separated
   by an edit distance of at least 3.

(There are other schemes for encoding bits as pronounceable but meaningless
"words", such as
[FIPS 181](http://csrc.nist.gov/publications/fips/fips181/fips181.pdf), but I'm
not concerned about those here.)

Passphrases are great because they take advantage of all this language-
processing machinery we carry around in our brains, making it possible to easily
remember lots of randomness. In this note I'm proposing yet another word list,
this one with the goal of constructing grammatically correct passphrases with
a given amount of entropy.

The WordCereal list consists of 2072 English words: 512 plural nouns, 512
transitive verbs, 512 adjectives, 512 adverbs, 8 plural determiners, 8
prepositions, and 8 conjunctions. The list is subject to the following
constraints, inspired by word lists that have come before (particularly from the
EFF).

1. Individual code words are separated by a Levenshtein edit distance of at
   least 3. This makes it possible for implementations to detect and correct at
   least 1 deleted letter, inserted letter, or swapped letter.
2. As a set, the code words are prefix free. This guarantees a bijective mapping
   between concatenated lists of code words and lists of bits, so that entropy
   is preserved. (For good measure the list is suffix free as well.)
3. As a set, the code words have unique initial 5-grams.
4. The initial 3-grams of code words map uniquely to encoded bits.
5. Code words are phonetically "distinct" pairwise. This constraint is fuzzier.
   I take it to mean that the phonetic distance between any two words, as lists
   of syllables of IPA characters, is at least 1, and that no word is a phonetic
   prefix or suffix of another.
6. Our code words of a given part of speech come in lists of two types: one of
   words with an even number of syllables, and one of words with an odd number
   of syllables. In this way the (parity of the) number of syllables in the code
   words can be used to detect omitted words.

In addition, we impose the following.

1. Use only the lower-case Latin alphabet, with no punctuation.
2. Avoid words that are commonly considered vulgar (there are a lot of these).
3. Avoid gendered, racist, or ablist words (there are a lot of these too).
4. Avoid place names, proper nouns, and trademarks.
5. Avoid words that have homophones of the same part of speech (naughty/knotty,
   insure/ensure).
6. Avoid commonly misspelled words.
7. Avoid words with multiple common spellings (donuts/doughnuts).
8. Avoid words with ambiguous pronunciations (within a dialect) or ambiguous
   division into syllables.

When I started this project it was not obvious that such a list existed. It
turns out it does, and I make no claim that the one presented here is optimal.
For this reason the WordCereal list is versioned, to allow for usability
improvements.

This text is literate Haskell. Along the way we'll build a program which
verifies the combinatorial properties of our word list and actually encodes
bits. To this end we need to start with some boilerplate.

> module Main where
> 
> import Data.List
> import Data.Maybe
> import Data.Random.RVar
> import Data.Random.Extras
> import Data.Random.Source.DevRandom
> import System.Exit
> import System.Environment
> import Control.Monad.Writer
> import Control.Applicative
> import Test.QuickCheck

In the remainder, we'll do the following:

1. Say a few words about entropy, the measure of randomness.
2. Give a simplified model of English grammar for use with WordCereal.
3. Specify the format of the WordCereal list, and write code to parse it.
4. Write code to verify the combinatorial properties of the word list.
5. Build a very simple tool for encoding bits as grammatically correct phrases
   at the command line.


Entropy
=======

Recall that *entropy* is the metric typically used to talk about the security of
a password, and it's measured in *bits*. Kolmogorov complexity notwithstanding
it's not quite correct to talk about individual passwords as being high or low
entropy; entropy depends on the method used to construct the password. The idea
is that a password is only really "secure" if it's hard to guess *even if* we
assume an attacker knows everything about how it was constructed except for the
secret password itself. For example, if we make our password the result of 40
consecutive coin flips, we have to assume the attacker knows this.

I find it helpful to think of entropy in terms of the game
[Twenty Questions](https://en.wikipedia.org/wiki/Twenty_Questions). In this
game, one player chooses a secret item and the other tries to guess what it is
by asking yes/no questions. Say we have a method for choosing the secret item.
The entropy of our method (in bits) is the minimum number of yes/no questions
that guarantee a win for the guesser. For example, if the entropy of our method
is 10 bits, they may get lucky and find the secret in *fewer* than 10 questions,
but they'll never need *more* than 10.

So the entropy of a password is an upper bound on its hardness, not a lower
bound. This sounds pessimistic. On the other hand, there are reasons to expect
that classical computers are practically incapable of ever brute-forcing a
secret with more than 256 bits of entropy. So the amount of entropy we need in
practice isn't ridiculously large.

I'll define a class ``Entropizable`` with a single function, ``entropy``, for
measuring the entropy (in bits) of things that are entropizable.

> class Entropizable t where
>   entropy :: t -> Int
> 
> instance Entropizable t => Entropizable [t] where
>   entropy = sum . map entropy

How exactly is entropy measured? Suppose we choose a single item from a set of
$n$ distinct items. The entropy of our choice is $\log_2(n)$ bits. So if we
choose a single word from a list of, say, 256 words, this choice has entropy
$\log_2(256) = 8$ bits. Now entropy is additive in the sense that if we choose
one item from a list of $n$, and another item from another list of $m$, the
entropy of both choices is $\log_2(n) + \log_2(m)$. This is where the `sum`
comes from in our definition of entropy for lists.


Grammar
=======

Chomsky's theory of
[generative grammars](https://en.wikipedia.org/wiki/Generative_grammar) is a
useful mechanism for building randomized sentences. A generative grammar defines
a set of valid sentences using one or more *production rules*. For example, at
its most basic, an English sentence might consist of a subject noun phrase,
followed by a verb phrase, followed by an object noun phrase. Symbolically we
can model this like so.

    S -> N_P V_P N_P

Now a noun phrase might consist of either a concrete noun like *puppies* or
*garbanzos*, or a determiner word like *two* or *those* followed by a concrete
noun, or a concrete adjective followed by a concrete noun, or a noun phrase
followed by a prepositional phrase, or any of several other possibilities. We
might model this symbolically like so.

    N_P -> Noun | Det Noun | Adj Noun | Noun P_P | ...

Similarly, a verb phrase might be a concrete verb, or an adverb followed by a
concrete verb, or something else.

    V_P -> Verb | Adv Verb | ...

The full story of Chomsky's generative grammars is more complicated (of course)
but this is good enough for us. 

For this simplified model, we will use just seven parts of speech: plural nouns,
transitive verbs, adjectives, adverbs, prepositions, determiners, and
conjunctions. The last two are used to make sentences more "natural" sounding
and provide only nominal additional entropy.

> data PartOfSpeech
>   = Noun | Verb | Adj | Adv | Prep | Det | Conj
>   deriving (Eq, Ord)
> 
> instance Show PartOfSpeech where
>   show x = case x of
>     Noun -> "N"
>     Verb -> "V"
>     Adj  -> "J"
>     Adv  -> "A"
>     Prep -> "P"
>     Det  -> "D"
>     Conj -> "C"
> 
> instance Entropizable PartOfSpeech where
>   entropy x = case x of
>     Noun -> 8
>     Verb -> 8
>     Adj  -> 8
>     Adv  -> 8
>     Prep -> 2
>     Det  -> 2
>     Conj -> 2

For our purposes a sentence is a list of parts of speech which we define to be
grammatically correct. We can define our list of sentences using syntax that
looks almost like Chomsky's production rules. This list includes 83,232
distinct sentence structures with entropy ranging from 24 to 146 bits.

> sentences :: [[PartOfSpeech]]
> sentences =
>   let
>     n_c =
>       [ [Noun]
>       , [Det, Noun]
>       , [Adj, Noun]
>       , [Det, Adj, Noun]
>       ]
> 
>     v_c =
>       [ [Verb]
>       , [Adv, Verb]
>       ]
> 
>     p_p = map (Prep:) n_c
> 
>     (&+) xss yss = do
>       xs <- xss
>       ys <- yss
>       return $ xs ++ ys
> 
>     simp = concat
>       [ n_c &+        v_c &+ n_c
>       , n_c &+ p_p &+ v_c &+ n_c
>       , n_c &+        v_c &+ n_c &+ p_p
>       ]
> 
>   in
>     sortOn entropy $ concat
>       [ simp
>       , simp &+ [[Conj]] &+ simp
>       ]
> 
> -- my Data.List is old
> sortOn :: (Ord a) => (t -> a) -> [t] -> [t]
> sortOn f = sortBy (\x y -> compare (f x) (f y))

We also define a helper function that chooses a sentence structure with (at
least) a given entropy.

> randomSentence :: Int -> IO [PartOfSpeech]
> randomSentence k = do
>   let (x:xs) = dropWhile (\s -> entropy s < k) sentences
>   let ys = takeWhile (\s -> entropy s == entropy x) (x:xs)
>   runRVar (choice ys) DevRandom

And for fun, ``writeSentences`` writes all of our sentence structures to a file.

> encodeSentence :: [PartOfSpeech] -> String
> encodeSentence ps = concat
>   [ show $ entropy ps
>   , ","
>   , concatMap show ps
>   ]
> 
> writeSentences :: FilePath -> IO ()
> writeSentences path = do
>   let xs = sentences
>   appendFile path $ unlines $ map encodeSentence xs


Words
=====

We have a function, ``randomSentence``, that constructs a random sentence
structure with a given amount of entropy -- provided we have an appropriate word
list. Now we will model the word list itself and see how to validate that it has
the properties we want.

Each word in our list will have:

1. a (canonical) spelling,
2. a (canonical) part of speech,
3. a (canonical) syllable count parity (even or odd),
4. a (canonical) pronunciation, and
5. a numeric value, expressed in binary.

We can model this as a record like so.

> data Word = Word
>   { spelling :: String
>   , function :: PartOfSpeech
>   , sylCount :: Parity
>   , phonemes :: Pronunciation
>   , numValue :: [Bit]
>   }

``Parity`` is simple enough.

> data Parity = Even | Odd deriving Eq
> 
> parity :: Int -> Parity
> parity k = if (k`rem`2) == 0
>   then Even
>   else Odd

Now ``numValue`` is a list of bits, which will be encoded as base 4 (for
determiners, prepositions, and conjunctions) or base 16 (nouns, verbs,
adjectives, and adverbs) in the word list. There's probably a more elegant way
to do this, but brute force is fine for now.

> data Bit = Zero | One
>   deriving (Eq, Ord, Show)
> 
> fromBase4 :: [Char] -> Either Char [Bit]
> fromBase4 = fmap concat . sequence . map digit
>   where
>     digit c = case c of
>       '0' -> return [Zero, Zero]
>       '1' -> return [Zero, One ]
>       '2' -> return [One,  Zero]
>       '3' -> return [One,  One ]
>       _   -> Left c
> 
> fromBase16 :: [Char] -> Either Char [Bit]
> fromBase16 = fmap concat . sequence . map digit 
>   where
>     digit c = case c of
>       '0' -> return [Zero, Zero, Zero, Zero]
>       '1' -> return [Zero, Zero, Zero, One ]
>       '2' -> return [Zero, Zero, One,  Zero]
>       '3' -> return [Zero, Zero, One,  One ]
>       '4' -> return [Zero, One,  Zero, Zero]
>       '5' -> return [Zero, One,  Zero, One ]
>       '6' -> return [Zero, One,  One,  Zero]
>       '7' -> return [Zero, One,  One,  One ]
>       '8' -> return [One,  Zero, Zero, Zero]
>       '9' -> return [One,  Zero, Zero, One ]
>       'a' -> return [One,  Zero, One,  Zero]
>       'b' -> return [One,  Zero, One,  One ]
>       'c' -> return [One,  One,  Zero, Zero]
>       'd' -> return [One,  One,  Zero, One ]
>       'e' -> return [One,  One,  One,  Zero]
>       'f' -> return [One,  One,  One,  One ]
>       _   -> Left c

It will be handy later to construct streams of "random" bits, so we'll define
helpers for this here.

> instance Arbitrary Bit where
>   arbitrary = elements [Zero, One]
> 
> randomBits :: IO [Bit]
> randomBits = generate infiniteList
> 
> getEntropy :: (Entropizable t) => [Bit] -> [t] -> [[Bit]]
> getEntropy _ [] = []
> getEntropy src (x:xs) =
>   let k = entropy x in
>   let k = entropy x in
>   (take k src) : getEntropy (drop k src) xs

Finally, we'll take the simplified view that a pronunciation is a list of
syllables, where a syllable is a list of phonemes represented by IPA characters
and possibly a "stress". No doubt linguists would shudder at this. :)

> type Pronunciation = [Syllable]
> 
> data Syllable = Syllable
>   { stress :: Stress
>   , phones :: [Phoneme]
>   } deriving Eq
> 
> type Phoneme = String
> 
> data Stress
>   = Primary | Secondary | Unstressed
>   deriving Eq

Now a ``WordList`` is a list of words (shock) which is further divided on (1)
part of speech and (2) the *parity* (even or odd) of the syllable count.

> data WordList = WordList
>   { nou_e :: [Word], nou_o :: [Word]
>   , vrb_e :: [Word], vrb_o :: [Word]
>   , jec_e :: [Word], jec_o :: [Word]
>   , adv_e :: [Word], adv_o :: [Word]
>   , prp_e :: [Word], prp_o :: [Word]
>   , det_e :: [Word], det_o :: [Word]
>   , con_e :: [Word], con_o :: [Word]
>   }

The helper function ``makeWordList`` will take a list of ``Word``s and partition
it by part of speech and syllable count parity. ``subLists`` returns a list of
lists of words by part of speech and syllable count parity, and ``allWords``
turns a ``WordList`` back into a ``[Word]``.

> makeWordList :: [Word] -> WordList
> makeWordList = foldr addWord empty
>   where
>     empty :: WordList
>     empty = WordList
>       { nou_e = [], nou_o = [], vrb_e = [], vrb_o = []
>       , jec_e = [], jec_o = [], adv_e = [], adv_o = []
>       , prp_e = [], prp_o = [], det_e = [], det_o = []
>       , con_e = [], con_o = []
>       }
> 
> -- not pretty, but it does the job :)
> addWord :: Word -> WordList -> WordList
> addWord w l =
>   case (function w, sylCount w) of
>     (Noun, Even) -> l { nou_e = w : nou_e l }
>     (Noun, Odd)  -> l { nou_o = w : nou_o l }
>     (Verb, Even) -> l { vrb_e = w : vrb_e l }
>     (Verb, Odd)  -> l { vrb_o = w : vrb_o l }
>     (Adj,  Even) -> l { jec_e = w : jec_e l }
>     (Adj,  Odd)  -> l { jec_o = w : jec_o l }
>     (Adv,  Even) -> l { adv_e = w : adv_e l }
>     (Adv,  Odd)  -> l { adv_o = w : adv_o l }
>     (Prep, Even) -> l { prp_e = w : prp_e l }
>     (Prep, Odd)  -> l { prp_o = w : prp_o l }
>     (Det,  Even) -> l { det_e = w : det_e l }
>     (Det,  Odd)  -> l { det_o = w : det_o l }
>     (Conj, Even) -> l { con_e = w : con_e l }
>     (Conj, Odd)  -> l { con_o = w : con_o l }
> 
> subLists :: WordList -> [[Word]]
> subLists x = map ($ x)
>   [ nou_e, nou_o, vrb_e, vrb_o
>   , jec_e, jec_o, adv_e, adv_o
>   , prp_e, prp_o, det_e, det_o
>   , con_e, con_o
>   ]
> 
> allWords :: WordList -> [Word]
> allWords = concat . subLists

The ``stats`` function will be used later to display basic info about a
``WordList``. (This was more useful while the list was still being constructed.)

> stats :: WordList -> IO ()
> stats list = do
>   putStrLn "counts"
>   putStrLn $ "-- nou-e: " ++ prog (length $ nou_e list) 256
>   putStrLn $ "-- nou-o: " ++ prog (length $ nou_o list) 256
>   putStrLn $ "-- vrb-e: " ++ prog (length $ vrb_e list) 256
>   putStrLn $ "-- vrb-o: " ++ prog (length $ vrb_o list) 256
>   putStrLn $ "-- jec-e: " ++ prog (length $ jec_e list) 256
>   putStrLn $ "-- jec-o: " ++ prog (length $ jec_o list) 256
>   putStrLn $ "-- adv-e: " ++ prog (length $ adv_e list) 256
>   putStrLn $ "-- adv-o: " ++ prog (length $ adv_o list) 256
>   putStrLn $ "-- prp-e:   " ++ prog (length $ prp_e list) 4
>   putStrLn $ "-- prp-o:   " ++ prog (length $ prp_o list) 4
>   putStrLn $ "-- det-e:   " ++ prog (length $ det_e list) 4
>   putStrLn $ "-- det-o:   " ++ prog (length $ det_o list) 4
>   putStrLn $ "-- con-e:   " ++ prog (length $ con_e list) 4
>   putStrLn $ "-- con-o:   " ++ prog (length $ con_o list) 4
>   putStrLn $ "totals"
>   putStrLn $ "-- word:  " ++ prog (length $ allWords list) 2072
>   where
>     prog k n = show k ++ " " ++ show (k*100 `div` n) ++ "%"


Parsing
=======

We'll store our word list as a tab-delimited list of records with the following
fields:

1. Part of speech, followed by a hyphen, and the syllable parity ('e' for even,
   'o' for odd).
2. Numeric value in hexadecimal or base 4, depending on the part of speech.
3. Canonical spelling.
4. Canonical pronunciation, in IPA, with syllables separated by backslashes.

This part is pretty boring. First a helper to parse tab-delimited strings.

> untab :: String -> [String]
> untab cs = case span (/= '\t') cs of
>   (a,'\t':as) -> a : untab as
>   (a,[])      -> [a]

Part of speech:

> readPOS :: String -> Either Error PartOfSpeech
> readPOS x = case x of
>   "nou" -> return Noun
>   "vrb" -> return Verb
>   "jec" -> return Adj
>   "adv" -> return Adv
>   "prp" -> return Prep
>   "det" -> return Det
>   "con" -> return Conj
>   _     -> Left $ MalformedPartOfSpeech x

Parity:

> readParity :: Char -> Either Error Parity
> readParity c = case c of
>   'o' -> return Odd
>   'e' -> return Even
>   _   -> Left $ MalformedParity [c]

Numeric value:

> readHex :: String -> String -> Either Error [Bit]
> readHex spell x = case x of
>   [u] -> case fromBase4 [u] of
>     Right b -> return b
>     Left c  -> Left $ InvalidHexDigits spell [c]
>   [u,v] -> case fromBase16 [u,v] of
>     Right b -> return b
>     Left c  -> Left $ InvalidHexDigits spell [c]
>   _ -> Left $ InvalidHexDigits spell x

Spelling:

> readStem :: String -> Either Error String
> readStem s = if all (`elem` ['a'..'z']) s
>   then return s
>   else Left $ InvalidCharacters s

Pronunciation:

> -- tokenize a string of english IPA symbols
> readIPA :: String -> String -> Either Error [Phoneme]
> readIPA stem x = read x
>   where
>     read x = case x of
>       []    -> return []
>       [c]   -> readSingle [c]
>       [c,d] -> readDouble [c,d]
>       _     -> readTriple x
> 
>     single =
>       "ɑæʌɛeɪiʊəɚɝɒɔuʧʤbdðθfɡhjklɫmɱnŋɹsʃʔɾptvwzʒ"
> 
>     double =
>       [ "ɑː", "uː", "ɔː", "ɚː", "iː"
>       , "eɪ", "aɪ", "aʊ", "ju", "oʊ", "ɔɪ", "jʌ"
>       , "ɑɹ", "ɛɚ", "iɚ", "oɹ", "jɚ"
>       , "kʰ", "pʰ", "tʰ"
>       ]
> 
>     triple =
>       [ "juː"
>       ]
> 
>     readTriple :: String -> Either Error [Phoneme]
>     readTriple (c:d:e:w) = if elem [c,d,e] triple
>       then ([c,d,e]:) <$> read w
>       else readDouble (c:d:e:w)
> 
>     readDouble :: String -> Either Error [Phoneme]
>     readDouble (c:d:w) = if elem [c,d] double
>       then ([c,d]:) <$> read w
>       else readSingle (c:d:w)
> 
>     readSingle :: String -> Either Error [Phoneme]
>     readSingle (c:w) = if elem c single
>       then ([c]:) <$> read w
>       else Left $ UnrecognizedPhoneme stem [c]
> 
> -- parse a syllable
> readSyllable :: String -> String -> Either Error Syllable
> readSyllable stem x = case x of
>   ('ˈ':w) -> do
>     ps <- readIPA stem w
>     return $ Syllable Primary ps
>   ('ˌ':w) -> do
>     ps <- readIPA stem w
>     return $ Syllable Secondary ps
>   _ -> do
>     ps <- readIPA stem x
>     return $ Syllable Unstressed ps
> 
> readPronunciation :: String -> String -> Either Error Pronunciation
> readPronunciation stem x = do
>   let
>     -- split on '/' chars
>     foo :: String -> [String] -> Either Error [String]
>     foo ('/':[]) ps = return ps
>     foo ('/':cs) ps = do
>       let (p,ds) = span (/= '/') cs
>       foo ds (p:ps)
>     foo z ps = Left $ BadPronunciation x
> 
>   chunks <- fmap reverse $ foo x []
>   syls   <- sequence $ map (readSyllable stem) chunks
>   return syls

An entire entry:

> readEntry :: String -> Either Error Word
> readEntry ln = case untab ln of
>   [(x:y:z:'-':n:[]),hex,spell,sound] ->
>     Word
>      <$> readStem spell
>      <*> readPOS [x,y,z]
>      <*> readParity n
>      <*> readPronunciation spell sound
>      <*> readHex spell hex
>   _ -> Left $ MalformedEntry ln

An entire file:

> readWordList :: String -> Either Error WordList
> readWordList =
>   fmap makeWordList . sequence . map readEntry . lines

And finally, a helper to read and parse a word list file from a given path.

> readWordListFile :: FilePath -> IO WordList
> readWordListFile path = do
>   raw <- readFile path
>   case readWordList raw of
>     Left err -> do
>       putStrLn $ show err
>       exitFailure
>     Right x -> return x

Woo! So now ``readWordListFile`` will take the path to a word list and parse it.
Moreover, if anything fails we get an error message.


Validation
==========

Now we're prepared to validate the combinatorial properties of our word list.
This will take place within the ``Writer`` monad, with "writes" of type
``Output``. We'll provide output of two types: messages are simply output for
the user, while errors indicate showstopping failures. We'll save the exact
nature of this ``Error`` type for later.

> data Output = Msg String | Err Error
> 
> instance Show Output where
>   show (Msg x) = x
>   show (Err x) = ">>> " ++ show x
> 
> message :: String -> Writer [Output] ()
> message x = tell [Msg x]
> 
> snafu :: Error -> Writer [Output] ()
> snafu x = tell [Err x]

Next we'll define helper functions for validating each property.


Length
------

Each word should be between 3 and 15 letters long.

> checkLength :: Word -> Writer [Output] ()
> checkLength w = do
>   let str = spelling w
>   let len = length str
>   if (3 <= len) && (len <= 15)
>     then return ()
>     else snafu $ BadLength str
> 
> validateLengths :: WordList -> Writer [Output] ()
> validateLengths list = do
>   message "Validating lengths"
>   mapM_ checkLength $ allWords list


Syllable Parity
---------------

Verify that even words have an even number of syllables, and odd words have an
odd number of syllables.

> checkSyllableCount :: Word -> Writer [Output] ()
> checkSyllableCount w =
>   if (sylCount w) == (parity $ length $ phonemes w)
>     then return ()
>     else snafu $ BadSyllables (spelling w)
> 
> validateSyllableCount :: WordList -> Writer [Output] ()
> validateSyllableCount list = do
>   message "Validating syllable counts"
>   mapM_ checkSyllableCount $ allWords list


Affixes
-------

Verify that no word is a prefix or suffix of any other.

> checkAffixes :: Word -> Word -> Writer [Output] ()
> checkAffixes u v = do
>   let x = spelling u
>   let y = spelling v
>   sequence_
>     [ if (isPrefixOf x y) || (isPrefixOf y x)
>         then snafu $ WordPrefix x y
>         else return ()
>     , if (isSuffixOf x y) || (isSuffixOf y x)
>         then snafu $ WordSuffix x y
>         else return ()
>     ]
> 
> allPairs :: [a] -> [(a,a)]
> allPairs []     = []
> allPairs (a:as) = [(a,b) | b <- as] ++ allPairs as
> 
> validateAffixes :: WordList -> Writer [Output] ()
> validateAffixes list = do
>   message "Validating affixes"
>   mapM_ (uncurry checkAffixes) $ allPairs $ allWords list


Initial Trigrams
----------------

Here we check that (1) no two words with the same part of speech and parity have
the same initial 3-grams, and (2) no entropy 2 word has the same initial 3-gram
as an entropy 8 word (and vice versa).

> checkTrigrams :: Word -> Word -> Writer [Output] ()
> checkTrigrams u v = do
>   let su = spelling u
>   let sv = spelling v
>   if (take 3 su) == (take 3 sv)
>     then snafu $ BadTrigrams su sv
>     else return ()
> 
> validateTrigrams :: WordList -> Writer [Output] ()
> validateTrigrams list = do
>   message "Validating initial trigrams"
>   sequence_
>     [ mapM_ (uncurry checkTrigrams) $ allPairs xs | xs <- subLists list ]
> 
>   let
>     us = concatMap ($ list)
>       [ det_e, det_o, prp_e, prp_o, con_e, con_o
>       ]
> 
>     vs = concatMap ($ list)
>       [ nou_e, nou_o, vrb_e, vrb_o
>       , jec_e, jec_o, adv_e, adv_o
>       ]
> 
>   mapM_ (uncurry checkTrigrams) [(x,y) | x <- us, y <- vs]


Numeric Values
---------------

Here we check that (1) two words with the same initial 3-grams have the same
numeric value and (2) two words with the same part of speech and parity have
different numeric values.

> checkHex :: Word -> Word -> Writer [Output] ()
> checkHex u v = do
>   let (a,su) = (numValue u, spelling u)
>   let (b,sv) = (numValue v, spelling v)
>   if ((take 3 su) == (take 3 sv)) && (a /= b)
>     then snafu $ BadHexTrigrams su sv
>     else return ()
> 
> checkDiffHex :: Word -> Word -> Writer [Output] ()
> checkDiffHex u v = if (numValue u) == (numValue v)
>   then snafu $ BadSameHex (spelling u) (spelling v)
>   else return ()
> 
> validateHex :: WordList -> Writer [Output] ()
> validateHex list = do
>   message "Validating hex values"
>   mapM_ (uncurry checkHex) $ allPairs $ allWords list
> 
>   sequence_
>     [ mapM_ (uncurry checkDiffHex) $ allPairs xs | xs <- subLists list ]


Initial Pentagrams
------------------

No two words have the same initial 5-grams.

> checkPentagrams :: Word -> Word -> Writer [Output] ()
> checkPentagrams u v = do
>   let su = spelling u
>   let sv = spelling v
>   if (take 5 su) == (take 5 sv)
>     then snafu $ BadPentagrams su sv
>     else return ()
> 
> validatePentagrams :: WordList -> Writer [Output] ()
> validatePentagrams list = do
>   message "Validating initial pentagrams"
>   mapM_ (uncurry checkPentagrams) $ allPairs $ allWords list


Edit Distance
-------------

The edit distance between any two words is at least 3.

We'll use the [Levenshtein](https://wiki.haskell.org/Edit_distance) string
metric. This implementation cribbed from the
[Haskell Wiki](https://wiki.haskell.org/Edit_distance).

> dist :: Eq a => [a] -> [a] -> Int
> dist a b =
>   let
>     lab :: Int
>     lab = length a - length b
> 
>     min3 :: Int -> Int -> Int -> Int
>     min3 x y z = if x < y then x else min y z
> 
>     oneDiag a b above below = thisdiag
>       where
>         doDiag [] _ _ _ _ = []
>         doDiag _ [] _ _ _ = []
>         doDiag (ach:as) (bch:bs) nw n w =
>           me : (doDiag as bs me (tail n) (tail w))
>           where
>             me = if ach == bch
>               then nw
>               else 1 + min3 (head w) nw (head n)
> 
>         thisdiag = firstelt : doDiag a b firstelt above (tail below)
>           where firstelt = 1 + head below
> 
>     eachDiag a [] _ = []
>     eachDiag a (_:bs) (x:xs) =
>       oneDiag a bs nextDiag x : eachDiag a bs xs
>       where nextDiag = head (tail xs)
> 
>     uppers = eachDiag a b (mainDiag : uppers) -- upper diagonals
>     lowers = eachDiag b a (mainDiag : lowers) -- lower diagonals
>     mainDiag = oneDiag a b (head uppers) (-1 : head lowers)
> 
>   in
>     last $ if lab == 0
>       then mainDiag
>       else if lab > 0
>         then lowers !! (lab - 1)
>         else uppers !! (-1 - lab)
> 
> checkEditDistance :: Word -> Word -> Writer [Output] ()
> checkEditDistance u v = do
>   let x = spelling u
>   let y = spelling v
>   if (abs $ (length x) - (length y)) >= 3
>     then return ()
>     else if (dist x y) >= 3
>       then return ()
>       else snafu $ BadEditDist x y
> 
> validateEditDistance :: WordList -> Writer [Output] ()
> validateEditDistance list = do
>   message "Validating edit distance"
>   mapM_ (uncurry checkEditDistance) $ allPairs $ allWords list


Phonetic Distance
-----------------

The edit distance between any two pronunciations (as lists of syllables) is at
least 1.

> checkPhoneticEditDistance :: Word -> Word -> Writer [Output] ()
> checkPhoneticEditDistance u v = do
>   let x = phonemes u
>   let y = phonemes v
>   if (abs $ (length x) - (length y)) >= 1
>     then return ()
>     else if (dist x y) >= 1
>       then return ()
>       else snafu $ BadPhoneticDistance (spelling u) (spelling v)
> 
> validatePhoneticEditDistance :: WordList -> Writer [Output] ()
> validatePhoneticEditDistance list = do
>   message "Validating phonetic edit distance"
>   mapM_ (uncurry checkPhoneticEditDistance) $ allPairs $ allWords list


Phonetic Affixes
----------------

No pronunciation is a prefix or suffix of another.

> checkPhoneticAffixes :: Word -> Word -> Writer [Output] ()
> checkPhoneticAffixes u v = do
>   let x = map phones $ phonemes u
>   let y = map phones $ phonemes v
>   sequence_
>     [ if (isPrefixOf x y) || (isPrefixOf y x)
>         then snafu $ BadPhoneticAffix (spelling u) (spelling v)
>         else return ()
>     , if (isSuffixOf x y) || (isSuffixOf y x)
>         then snafu $ BadPhoneticAffix (spelling u) (spelling v)
>         else return ()
>     ]
> 
> validatePhoneticAffixes :: WordList -> Writer [Output] ()
> validatePhoneticAffixes list = do
>   message "Validating phonetic affixes"
>   mapM_ (uncurry checkPhoneticAffixes) $ allPairs $ allWords list


All Together
------------

> validate :: WordList -> Writer [Output] ()
> validate dict = do
>   validateLengths              dict
>   validateSyllableCount        dict
>   validateTrigrams             dict
>   validatePentagrams           dict
>   validatePhoneticAffixes      dict
>   validateAffixes              dict
>   validateHex                  dict
>   validatePhoneticEditDistance dict
>   validateEditDistance         dict

> validatePath :: FilePath -> IO ()
> validatePath path = do
>   dict <- readWordListFile path
>   try $ validate dict
>   stats dict

To validate a properly formatted word list, just give its full path to
``validatePath``.


Encoding
========

Now to actually encode bits as code words. First, ``encode`` looks up the word
with a given numeric value, part of speech, and parity.

> encode ::
>   WordList -> [Bit] -> PartOfSpeech -> Parity -> Writer [Output] String
> encode list val pos parity = case (pos,parity) of
>   (Noun, Odd)  -> encode' (nou_o list) val
>   (Noun, Even) -> encode' (nou_e list) val
>   (Verb, Odd)  -> encode' (vrb_o list) val
>   (Verb, Even) -> encode' (vrb_e list) val
>   (Adv,  Odd)  -> encode' (adv_o list) val
>   (Adv,  Even) -> encode' (adv_e list) val
>   (Adj,  Odd)  -> encode' (jec_o list) val
>   (Adj,  Even) -> encode' (jec_e list) val
>   (Det,  Odd)  -> encode' (det_o list) val
>   (Det,  Even) -> encode' (det_e list) val
>   (Prep, Odd)  -> encode' (prp_o list) val
>   (Prep, Even) -> encode' (prp_e list) val
>   (Conj, Odd)  -> encode' (con_o list) val
>   (Conj, Even) -> encode' (con_e list) val
>   where
>     encode' :: [Word] -> [Bit] -> Writer [Output] String
>     encode' words hex = do
>       let assoc = map (\x -> (numValue x, spelling x)) words
>       case lookup hex assoc of
>         Nothing -> (snafu $ MissingHex (show hex)) >> return "###"
>         Just s  -> return s

And encoding streams of parts of speech:

> encodeStream
>   :: WordList -> [[Bit]] -> [PartOfSpeech] -> Writer [Output] [String]
> encodeStream list vals poss = do
>   let parity = Odd : Even : parity
>   sequence $ zipWith3 (encode list) vals poss parity

Putting it together, ``encodeWith`` takes the path of a word list and a number
and generates a passphrase with the given amount of entropy.

> encodeWith :: FilePath -> Int -> IO ()
> encodeWith path ent = do
>   dict <- readWordListFile path
>   poss <- randomSentence ent
>   bits <- randomBits
>   let vals = getEntropy bits poss
>   xs <- try $ encodeStream dict vals poss
>   putStrLn $ unwords xs


Main
====

We'll wrap our encode function in an extremely simple main that takes two
command line arguments: the desired amount of entropy, and the (full) path of
the word list.

> main :: IO ()
> main = do
>   [ent,path] <- getArgs
>   encodeWith path (read ent)

And there you go. After compiling, call this program (``wordcereal``) with
two arguments, the number of bits of entropy desired and the path of the word
list on your system, and it will encode some entropy.


Errors
======

> data Error
>   = MalformedPartOfSpeech String
>   | MalformedParity String
>   | InvalidCharacters String
>   | InvalidHexDigits String String
>   | MalformedEntry String
>   | UnrecognizedPhoneme String String
>   | BadPronunciation String
>   | BadLength String
>   | BadSyllables String
>   | WordPrefix String String
>   | WordSuffix String String
>   | BadTrigrams String String
>   | BadHexTrigrams String String
>   | BadSameHex String String
>   | BadPentagrams String String
>   | BadEditDist String String
>   | BadPhoneticAffix String String
>   | BadPhoneticDistance String String
>   | MissingHex String
>   deriving Show
> 
> try :: Writer [Output] a -> IO a
> try x = do
>   let (out,err) = runWriter x
>   case err of
>     [] -> return out
>     ms -> do
>       mapM_ (putStrLn . show) ms
>       if any isError ms
>         then exitFailure
>         else return out
> 
> isError :: Output -> Bool
> isError x = case x of
>   Msg _ -> False
>   Err _ -> True
