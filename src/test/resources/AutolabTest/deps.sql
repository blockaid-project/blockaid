SELECT `assessment_user_data`.`id`, `assessments`.`course_id` FROM `assessments`, `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = `assessments`.`id`; SELECT `assessment_user_data`.`id`, `course_user_data`.`course_id` FROM `assessment_user_data`, `course_user_data` WHERE `assessment_user_data`.`course_user_datum_id` = `course_user_data`.`id`;
SELECT 1 FROM assessment_user_data, submissions WHERE assessment_user_data.latest_submission_id = submissions.id AND assessment_user_data.course_user_datum_id <> submissions.course_user_datum_id; SELECT 1 FROM assessment_user_data WHERE FALSE;
SELECT attachments.id, attachments.course_id FROM attachments; SELECT attachments.id, courses.id FROM attachments, assessments, courses WHERE attachments.assessment_id = assessments.id AND assessments.course_id = courses.id;
SELECT submissions.id, assessments.course_id FROM submissions JOIN assessments ON submissions.assessment_id = assessments.id; SELECT submissions.id, course_user_data.course_id FROM submissions JOIN course_user_data on submissions.course_user_datum_id = course_user_data.id;
SELECT watchlist_instances.id, watchlist_instances.course_id FROM watchlist_instances; SELECT watchlist_instances.id, course_user_data.course_id FROM watchlist_instances, course_user_data WHERE watchlist_instances.course_user_datum_id = course_user_data.id;
