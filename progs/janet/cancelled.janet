(defn work-no-cancel [] 
  (ev/sleep 2)
  (print "did some work!"))

(defn work []
  (try
    (work-no-cancel)
    ([err]
      (printf "work fiber cancelled with signal: %j" err))))

(defn main []
  (def task (ev/spawn (work)))
  (print "cancelling the work fiber...")
  (ev/sleep 1)
  (ev/cancel task :cancelled)
  (ev/sleep 1))

(main)
