(set-option :produce-models true)
(set-option :produce-interpolants true)
(set-logic AUFLIRA)
(set-info :source |
    SMT script generated on 2015/02/02 by Ultimate. http://ultimate.informatik.uni-freiburg.de/
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(define-sort ~size_t () Int)
(declare-fun |#offset~STRUCT#?n~INT?next~$Pointer$#~n| () Int)
(declare-fun |#offset~STRUCT#?n~INT?next~$Pointer$#~next| () Int)
(declare-fun |#sizeof~INT| () Int)
(declare-fun |#sizeof~$Pointer$| () Int)
(declare-fun |#to_int| (Real) Int)
(declare-fun |c_old(#NULL.base)| () Int)
(declare-fun |c_old(#NULL.base)_primed| () Int)
(declare-fun |c_#NULL.base| () Int)
(declare-fun |c_#NULL.base_primed| () Int)
(declare-fun |c_old(#NULL.offset)| () Int)
(declare-fun |c_old(#NULL.offset)_primed| () Int)
(declare-fun |c_#NULL.offset| () Int)
(declare-fun |c_#NULL.offset_primed| () Int)
(declare-fun |c_old(#memory_int)| () (Array Int (Array Int Int)))
(declare-fun |c_old(#memory_int)_primed| () (Array Int (Array Int Int)))
(declare-fun |c_#memory_int| () (Array Int (Array Int Int)))
(declare-fun |c_#memory_int_primed| () (Array Int (Array Int Int)))
(declare-fun |c_old(#memory_$Pointer$.base)| () (Array Int (Array Int Int)))
(declare-fun |c_old(#memory_$Pointer$.base)_primed| () (Array Int (Array Int Int)))
(declare-fun |c_#memory_$Pointer$.base| () (Array Int (Array Int Int)))
(declare-fun |c_#memory_$Pointer$.base_primed| () (Array Int (Array Int Int)))
(declare-fun |c_old(#memory_$Pointer$.offset)| () (Array Int (Array Int Int)))
(declare-fun |c_old(#memory_$Pointer$.offset)_primed| () (Array Int (Array Int Int)))
(declare-fun |c_#memory_$Pointer$.offset| () (Array Int (Array Int Int)))
(declare-fun |c_#memory_$Pointer$.offset_primed| () (Array Int (Array Int Int)))
(declare-fun |c_old(#valid)| () (Array Int Bool))
(declare-fun |c_old(#valid)_primed| () (Array Int Bool))
(declare-fun |c_#valid| () (Array Int Bool))
(declare-fun |c_#valid_primed| () (Array Int Bool))
(declare-fun |c_old(#length)| () (Array Int Int))
(declare-fun |c_old(#length)_primed| () (Array Int Int))
(declare-fun |c_#length| () (Array Int Int))
(declare-fun |c_#length_primed| () (Array Int Int))
(declare-fun |c_append_#in~l.base| () Int)
(declare-fun |c_append_#in~l.base_primed| () Int)
(declare-fun |c_append_#in~l.offset| () Int)
(declare-fun |c_append_#in~l.offset_primed| () Int)
(declare-fun |c_append_#in~n| () Int)
(declare-fun |c_append_#in~n_primed| () Int)
(declare-fun |c_append_#res.base| () Int)
(declare-fun |c_append_#res.base_primed| () Int)
(declare-fun |c_append_#res.offset| () Int)
(declare-fun |c_append_#res.offset_primed| () Int)
(declare-fun |c_append_#t~ret1.base| () Int)
(declare-fun |c_append_#t~ret1.base_primed| () Int)
(declare-fun |c_append_#t~ret1.offset| () Int)
(declare-fun |c_append_#t~ret1.offset_primed| () Int)
(declare-fun c_append_~l.base () Int)
(declare-fun c_append_~l.base_primed () Int)
(declare-fun c_append_~l.offset () Int)
(declare-fun c_append_~l.offset_primed () Int)
(declare-fun c_append_~n () Int)
(declare-fun c_append_~n_primed () Int)
(declare-fun c_append_~new_el~8.base () Int)
(declare-fun c_append_~new_el~8.base_primed () Int)
(declare-fun c_append_~new_el~8.offset () Int)
(declare-fun c_append_~new_el~8.offset_primed () Int)
(declare-fun c_append_~tmp~8.base () Int)
(declare-fun c_append_~tmp~8.base_primed () Int)
(declare-fun c_append_~tmp~8.offset () Int)
(declare-fun c_append_~tmp~8.offset_primed () Int)
(declare-fun |c_allocate_memory_#res.base| () Int)
(declare-fun |c_allocate_memory_#res.base_primed| () Int)
(declare-fun |c_allocate_memory_#res.offset| () Int)
(declare-fun |c_allocate_memory_#res.offset_primed| () Int)
(declare-fun |c_allocate_memory_#t~malloc0.base| () Int)
(declare-fun |c_allocate_memory_#t~malloc0.base_primed| () Int)
(declare-fun |c_allocate_memory_#t~malloc0.offset| () Int)
(declare-fun |c_allocate_memory_#t~malloc0.offset_primed| () Int)
(declare-fun c_allocate_memory_~tmp~5.base () Int)
(declare-fun c_allocate_memory_~tmp~5.base_primed () Int)
(declare-fun c_allocate_memory_~tmp~5.offset () Int)
(declare-fun c_allocate_memory_~tmp~5.offset_primed () Int)
(declare-fun c_allocate_memory_~__cil_tmp2~5 () Int)
(declare-fun c_allocate_memory_~__cil_tmp2~5_primed () Int)
(declare-fun c_~malloc_~size () Int)
(declare-fun c_~malloc_~size_primed () Int)
(declare-fun |c_~malloc_#res.base| () Int)
(declare-fun |c_~malloc_#res.base_primed| () Int)
(declare-fun |c_~malloc_#res.offset| () Int)
(declare-fun |c_~malloc_#res.offset_primed| () Int)
(declare-fun |c_read~int_#ptr.base| () Int)
(declare-fun |c_read~int_#ptr.base_primed| () Int)
(declare-fun |c_read~int_#ptr.offset| () Int)
(declare-fun |c_read~int_#ptr.offset_primed| () Int)
(declare-fun |c_read~int_#sizeOfReadType| () Int)
(declare-fun |c_read~int_#sizeOfReadType_primed| () Int)
(declare-fun |c_read~int_#value| () Int)
(declare-fun |c_read~int_#value_primed| () Int)
(declare-fun |c_write~int_#value| () Int)
(declare-fun |c_write~int_#value_primed| () Int)
(declare-fun |c_write~int_#ptr.base| () Int)
(declare-fun |c_write~int_#ptr.base_primed| () Int)
(declare-fun |c_write~int_#ptr.offset| () Int)
(declare-fun |c_write~int_#ptr.offset_primed| () Int)
(declare-fun |c_write~int_#sizeOfWrittenType| () Int)
(declare-fun |c_write~int_#sizeOfWrittenType_primed| () Int)
(declare-fun |c_read~$Pointer$_#ptr.base| () Int)
(declare-fun |c_read~$Pointer$_#ptr.base_primed| () Int)
(declare-fun |c_read~$Pointer$_#ptr.offset| () Int)
(declare-fun |c_read~$Pointer$_#ptr.offset_primed| () Int)
(declare-fun |c_read~$Pointer$_#sizeOfReadType| () Int)
(declare-fun |c_read~$Pointer$_#sizeOfReadType_primed| () Int)
(declare-fun |c_read~$Pointer$_#value.base| () Int)
(declare-fun |c_read~$Pointer$_#value.base_primed| () Int)
(declare-fun |c_read~$Pointer$_#value.offset| () Int)
(declare-fun |c_read~$Pointer$_#value.offset_primed| () Int)
(declare-fun c_~free_~addr.base () Int)
(declare-fun c_~free_~addr.base_primed () Int)
(declare-fun c_~free_~addr.offset () Int)
(declare-fun c_~free_~addr.offset_primed () Int)
(declare-fun |c_ULTIMATE.start_#t~ret12| () Int)
(declare-fun |c_ULTIMATE.start_#t~ret12_primed| () Int)
(declare-fun |c_malloc_#in~__size| () Int)
(declare-fun |c_malloc_#in~__size_primed| () Int)
(declare-fun |c_malloc_#res.base| () Int)
(declare-fun |c_malloc_#res.base_primed| () Int)
(declare-fun |c_malloc_#res.offset| () Int)
(declare-fun |c_malloc_#res.offset_primed| () Int)
(declare-fun |c_main_#res| () Int)
(declare-fun |c_main_#res_primed| () Int)
(declare-fun |c_main_#t~nondet4.n| () Int)
(declare-fun |c_main_#t~nondet4.n_primed| () Int)
(declare-fun |c_main_#t~nondet4.next.base| () Int)
(declare-fun |c_main_#t~nondet4.next.base_primed| () Int)
(declare-fun |c_main_#t~nondet4.next.offset| () Int)
(declare-fun |c_main_#t~nondet4.next.offset_primed| () Int)
(declare-fun |c_main_#t~ret7.base| () Int)
(declare-fun |c_main_#t~ret7.base_primed| () Int)
(declare-fun |c_main_#t~ret7.offset| () Int)
(declare-fun |c_main_#t~ret7.offset_primed| () Int)
(declare-fun |c_main_#t~ret8.base| () Int)
(declare-fun |c_main_#t~ret8.base_primed| () Int)
(declare-fun |c_main_#t~ret8.offset| () Int)
(declare-fun |c_main_#t~ret8.offset_primed| () Int)
(declare-fun |c_main_#t~mem9.base| () Int)
(declare-fun |c_main_#t~mem9.base_primed| () Int)
(declare-fun |c_main_#t~mem9.offset| () Int)
(declare-fun |c_main_#t~mem9.offset_primed| () Int)
(declare-fun |c_main_#t~mem10.base| () Int)
(declare-fun |c_main_#t~mem10.base_primed| () Int)
(declare-fun |c_main_#t~mem10.offset| () Int)
(declare-fun |c_main_#t~mem10.offset_primed| () Int)
(declare-fun |c_main_#t~mem11| () Int)
(declare-fun |c_main_#t~mem11_primed| () Int)
(declare-fun c_main_~l~11.base () Int)
(declare-fun c_main_~l~11.base_primed () Int)
(declare-fun c_main_~l~11.offset () Int)
(declare-fun c_main_~l~11.offset_primed () Int)
(declare-fun |c_main_~#m~11.base| () Int)
(declare-fun |c_main_~#m~11.base_primed| () Int)
(declare-fun |c_main_~#m~11.offset| () Int)
(declare-fun |c_main_~#m~11.offset_primed| () Int)
(declare-fun c_main_~__cil_tmp3~11.base () Int)
(declare-fun c_main_~__cil_tmp3~11.base_primed () Int)
(declare-fun c_main_~__cil_tmp3~11.offset () Int)
(declare-fun c_main_~__cil_tmp3~11.offset_primed () Int)
(declare-fun c_main_~__cil_tmp4~11.base () Int)
(declare-fun c_main_~__cil_tmp4~11.base_primed () Int)
(declare-fun c_main_~__cil_tmp4~11.offset () Int)
(declare-fun c_main_~__cil_tmp4~11.offset_primed () Int)
(declare-fun c_main_~__cil_tmp5~11 () Int)
(declare-fun c_main_~__cil_tmp5~11_primed () Int)
(declare-fun |c_write~$Pointer$_#value.base| () Int)
(declare-fun |c_write~$Pointer$_#value.base_primed| () Int)
(declare-fun |c_write~$Pointer$_#value.offset| () Int)
(declare-fun |c_write~$Pointer$_#value.offset_primed| () Int)
(declare-fun |c_write~$Pointer$_#ptr.base| () Int)
(declare-fun |c_write~$Pointer$_#ptr.base_primed| () Int)
(declare-fun |c_write~$Pointer$_#ptr.offset| () Int)
(declare-fun |c_write~$Pointer$_#ptr.offset_primed| () Int)
(declare-fun |c_write~$Pointer$_#sizeOfWrittenType| () Int)
(declare-fun |c_write~$Pointer$_#sizeOfWrittenType_primed| () Int)
(assert (= |#offset~STRUCT#?n~INT?next~$Pointer$#~n| 0))
(assert (= |#offset~STRUCT#?n~INT?next~$Pointer$#~next| 4))
(assert (= |#sizeof~INT| 4))
(assert (= |#sizeof~$Pointer$| 4))
(assert (distinct 

(or (not (= |#offset~STRUCT#?n~INT?next~$Pointer$#~next| 4)) (and (= |c_main_#t~ret7.offset| 0) (and (= (select |c_#length| |c_main_#t~ret7.base|) 8) (and (and (select |c_#valid| |c_main_#t~ret7.base|) (or (select |c_#valid| (select (select |c_#memory_$Pointer$.base| |c_main_#t~ret7.base|) 4)) (= (select |c_#length| (select (select |c_#memory_$Pointer$.base| |c_main_#t~ret7.base|) 4)) 8))) (and (and (or (select |c_#valid| |c_main_#t~ret7.base|) 

(forall ((var0 Int)) (<= 0 (+ (- 8) (+ (* (- 1) (select (select |c_#memory_$Pointer$.offset| |c_main_#t~ret7.base|) 4)) (select |c_#length| var0)))))) (select |c_#valid| |c_main_#t~ret7.base|)) (and (or (forall ((var0 Int)) (select |c_#valid| var0)) (or (<= 0 (+ (- 8) (+ (* (- 1) (select (select |c_#memory_$Pointer$.offset| |c_main_#t~ret7.base|) 4)) (select |c_#length| (select (select |c_#memory_$Pointer$.base| |c_main_#t~ret7.base|) 4))))) (<= 0 (+ (- 8) (+ (* (- 1) (select (select |c_#memory_$Pointer$.offset| |c_main_#t~ret7.base|) 4)) (select |c_#length| (select (select |c_#memory_$Pointer$.base| |c_main_#t~ret7.base|) 4))))))) (or (select |c_#valid| |c_main_#t~ret7.base|) (<= 0 (+ (- 8) (+ (* (- 1) (select (select |c_#memory_$Pointer$.offset| |c_main_#t~ret7.base|) 4)) (select |c_#length| (select (select |c_#memory_$Pointer$.base| |c_main_#t~ret7.base|) 4)))))))))))) 

(or (not (= |#offset~STRUCT#?n~INT?next~$Pointer$#~next| 4)) (and (= |c_main_#t~ret7.offset| 0) (and (= (select |c_#length| |c_main_#t~ret7.base|) 8) (and (and (select |c_#valid| |c_main_#t~ret7.base|) (or (select |c_#valid| (select (select |c_#memory_$Pointer$.base| |c_main_#t~ret7.base|) 4)) (= (select |c_#length| (select (select |c_#memory_$Pointer$.base| |c_main_#t~ret7.base|) 4)) 8))) (and (and (or (select |c_#valid| |c_main_#t~ret7.base|) 

(forall ((var0 Int)) (<= 0 (+ (- 8) (+ (* (- 1) (select (select |c_#memory_$Pointer$.offset| |c_main_#t~ret7.base|) 4)) (select |c_#length| var0)))))) (select |c_#valid| |c_main_#t~ret7.base|)) (and (or (forall ((var0 Int)) (select |c_#valid| var0)) (or (<= 0 (+ (- 8) (+ (* (- 1) (select (select |c_#memory_$Pointer$.offset| |c_main_#t~ret7.base|) 4)) (select |c_#length| (select (select |c_#memory_$Pointer$.base| |c_main_#t~ret7.base|) 4))))) (<= 0 (+ (- 8) (+ (* (- 1) (select (select |c_#memory_$Pointer$.offset| |c_main_#t~ret7.base|) 4)) (select |c_#length| (select (select |c_#memory_$Pointer$.base| |c_main_#t~ret7.base|) 4))))))) (or (select |c_#valid| |c_main_#t~ret7.base|) (<= 0 (+ (- 8) (+ (* (- 1) (select (select |c_#memory_$Pointer$.offset| |c_main_#t~ret7.base|) 4)) (select |c_#length| (select (select |c_#memory_$Pointer$.base| |c_main_#t~ret7.base|) 4))))))))))))))
(check-sat)
