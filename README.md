
# The MCC approaches the geometric mean of precision and recall as true negatives approach infinity.

This is a short paper that proves the G1 measure is equivalent to the limit of
the MCC as the number of true negatives approaches infinity.


### Abstract

The performance of a binary classifier is described by a confusion matrix with four entries: the number of true positives (TP), true negatives (TN), false positives (FP), and false negatives (FN).

The Matthew's Correlation Coefficient (MCC), F1, and Fowlkes--Mallows (FM) scores are scalars that summarize a confusion matrix.  Both the F1 and FM scores are based on only three of the four entries in the confusion matrix (they ignore TN).  In contrast, the MCC takes into account all four entries of the confusion matrix and thus can be seen as providing a more representative picture.

However, in object detection problems, measuring the number of true negatives is so large it is often intractable.  Thus we ask, what happens to the MCC as the number of true negatives approaches infinity?  This paper provides insight into the relationship between the MCC and FM score by proving that the FM-measure is equal to the limit of the MCC as the number of true negatives approaches infinity.



### Notes

This repo derived from the arxiv style Latex Template: https://github.com/kourgeorge/arxiv-style


### Links

The arXiv paper: https://arxiv.org/abs/2305.00594
