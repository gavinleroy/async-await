(defn mk-node [value &opt left right]
  {:value value 
   :left left 
   :right right})

(def tree 
  (mk-node 11 
           (mk-node 7 
                    (mk-node 3)
                    (mk-node 9))
           (mk-node 15 
                    (mk-node 13)
                    (mk-node 19
                             (mk-node 18)))))

(defn tree/iterate [tree]
  (defn looper [tree]
    (when tree 
      (looper (get tree :left))
      (yield (get tree :value))
      (looper (get tree :right))))
  (coro (looper tree)))

# (defn tree/iterate [tree]
#   (coro
#     (when tree 
#       (tree/iterate (get tree :left))
#       (yield (get tree :value))
#       (tree/iterate (get tree :right)))))

(each v (tree/iterate tree)
  (print v)
