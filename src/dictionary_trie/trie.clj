(ns dictionary-trie.trie)

(defstruct trie-node :word-fragment :type :children)

(defn type-switch [node type-val]
  (assoc node :type type-val))
(defn switch-to-word [node]
  (type-switch node :word))
(defn switch-to-nonword [node]
  (type-switch node :nonword))

; constructors 
(defn new-node
  ([type]
   (new-node type "" {}))
  ([type fragment]
   (new-node type fragment {}))
  ([type fragment children]
   (struct-map trie-node 
	       :word-fragment fragment, :type type, :children children)))
(def new-word-node (partial new-node :word))
(def new-nonword-node (partial new-node :nonword))
(defn top-node 
  "generate the degenerate top-level of the trie"
  []
  (new-node :top))


(defn consume-mutually 
  "mutually consume two strings, shoving the equal parts into an accumulator.
   at the end, return the accumulator and the targest-string leftovers and the source-string leftovers"
  [ source-string target-string  ]
  ; structural binding... neato
  (loop [[s & ss :as sStr] (seq source-string)
	[t & ts :as tStr] (seq target-string)
	accum []]
    (if (and (= t s)
	     (or (not (nil? t))
		 (not (nil? s))))
      (recur ss ts (conj accum t))
      [(seq accum) sStr tStr  ])))

(defstruct body-leg :match-type :target-leg :source-leg :body)

(defn twist-together
  [source-string target-string  ]
  (let [ [prefix  source target ] 
	 (consume-mutually source-string
			   target-string)
	 match-struct (partial struct-map body-leg :match-type)]
    (cond
     ; no match
     (nil? prefix)
     (match-struct  :no-match)
     ; they are the same word
     (and
      (nil? target)
      (nil? source))
     (match-struct  :same-word :body prefix)
     ; target is prefix of the source
     (nil? target)
     (match-struct  :target-is-prefix :body prefix :source-leg source)
     ; source is the prefix of the target
     (nil? source)
     (match-struct  :source-is-prefix :body prefix :target-leg target)
     ; they must share a prefix
     :default
     (match-struct  :shared-prefix :body prefix :target-leg target :source-leg source))))

;;; create a multimethod that handles our 5 situations.
(defmulti insert-node
  #(:match-type %2))
(defmethod insert-node :same-word
  [node match-data]
  (switch-to-word node))
; -- the following is guaranteed not to have something at the child node as we
; -- checked it above (in the add-word-to-trie method
(defmethod insert-node :target-is-prefix
  [{children :children :as node} 
   {[s & _ :as suffix] :source-leg :as match-data}]
  (assoc-in node [:children s]
	    (new-word-node suffix)))
; -- the following is for trie nodes where the source is smaller
(defmethod insert-node :source-is-prefix
  [{old-type :type children :children :as node}
   {body :body [t & _ :as target-suffix] :target-leg :as match-data}]
  (let [slid-node (conj node 
			{:word-fragment target-suffix
			:type old-type})]
    (new-word-node body
		   { t slid-node})))
(defmethod insert-node :shared-prefix
  [node
   {body :body 
   [s & _ :as source-suffix] :source-leg 
   [t & _ :as target-suffix] :target-leg 
   :as match-data}]
  (let [new-source-suffix-node (new-word-node source-suffix)
	new-target-suffix-node (conj node {:word-fragment target-suffix})
	new-children {s new-source-suffix-node, t new-target-suffix-node}]
    (new-nonword-node body new-children)))
  
(defmethod insert-node :no-match
  [node match-data]
  (println " very likely you should not be here"))


(defmulti add-word-to-trie 
	  (fn [word  trie] (:type trie)))
(defmethod add-word-to-trie :top 
  [[first-char & rest :as word] { children :children :as trie}]
  (assoc-in trie [:children first-char]
	    (if (contains? children first-char)
	      (add-word-to-trie word (children first-char))
	      (new-word-node word))))

;; standard case
(defmethod add-word-to-trie :default 
  [[source-first & rest :as source-word] 
   {target-word :word-fragment children :children :as node}]
  (let [{match-type                             :match-type,
	[source-suffix-k & _ :as source-suffix] :source-leg :as match-data}
	(twist-together source-word target-word)]
    (if (and (= :target-is-prefix
		match-type)
	     (contains? children source-suffix-k))
      (assoc-in node [:children source-suffix-k ]
		(add-word-to-trie source-suffix 
				  (children source-suffix-k)))
      (insert-node node match-data))))


(defstruct dot-path :from :to)
(defstruct dot-label :id :label)

(defn red-str [x]
  #(reduce str "" (x %)))

(defn generate-dot-label 
  [{type :type wf :word-fragment}]
  (let [is-a (partial = type)
	rstr (reduce str "" wf)]
    (cond
     (is-a :top)
     "&#8709;"
     (is-a :word)
     (str rstr "(*)")
     (is-a :nonword)
     rstr)))

(defn generate-dot
  [node path]
  (let [ generate-path-node     #(struct-map dot-path :from path :to (cons % path))
	 generate-children-dots (fn [[k v]] (generate-dot v (cons k path)))]
    (let [ my-dot-node       (struct-map dot-label :id path 
					 :label (generate-dot-label node))
	   my-paths          (map generate-path-node 
				  (keys (:children node)))
	   my-children-dots  (reduce concat (map generate-children-dots (seq (:children node))))]
      (concat (cons my-dot-node my-paths) my-children-dots))))
(defmulti show-dot
  #(cond
    (contains? % :from)
    :path
    (contains? % :id)
    :node))
(defmethod show-dot :path
  [dot]
  (str "\"" ((red-str :from) dot) "\"" "->"
       "\"" ((red-str :to) dot  ) "\""
       "[label=\" " (first (:to dot)) "\"]"))
(defmethod show-dot :node
  [dot]
  (str "\"" ((red-str :id) dot) "\"" 
       "[label=\"" ((red-str :label) dot) "\"]"))
(defn generate-pretty 
  [node]
  (reduce #(str %1 "\n" %2) (map show-dot (generate-dot node "_"))))
(defn generate-trie 
  ([ words node ]
   (reduce #(add-word-to-trie %2 %1) node words)) 
  ([ words ]
   (generate-trie words (top-node))))
  
(def test-words
     ["rebate" "reborn" "realize" "real" "relied" "rebates" "reb" "relief" "realizes" "redder" "red"])
(def test-trie
     (generate-trie test-words))
(defn query-node-with-path
  ( [source node]
    (query-node-with-path source node []))
  ([ [ s & _ :as source ]
    {type :type children :children wf :word-fragment :as node} 
    acc]
  (let [node-type? (partial  = (:type node))]
    (if (node-type? :top)
      (if (contains? children s)
	(recur source (children s) acc)
	[ false, acc])
      (let [match-data (twist-together source wf)
	    match-type? (partial = (:match-type match-data))]
	(cond
	 (match-type? :same-word)
	 (if (node-type? :word)
	   [true, (cons wf acc)]
	   [false, acc])
	 (match-type? :target-is-prefix)
	 (let [ {[s & _ :as suffix-string-source] :source-leg} match-data]
	   (if (contains? children s)
	     (recur suffix-string-source (children s) (cons wf acc))
	     [false, acc]))
	 :default
	 [false, acc]))))))
  
(def query-node #(let [ [val _] (query-node-with-path %1 %2)] val))

(def words-queried (map #(query-node % test-trie) test-words))