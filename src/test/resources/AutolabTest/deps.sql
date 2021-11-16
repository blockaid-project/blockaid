SELECT `assessment_user_data`.`id`, `assessments`.`course_id` FROM `assessments`, `assessment_user_data` WHERE `assessment_user_data`.`assessment_id` = `assessments`.`id`; SELECT `assessment_user_data`.`id`, `course_user_data`.`course_id` FROM `assessment_user_data`, `course_user_data` WHERE `assessment_user_data`.`course_user_datum_id` = `course_user_data`.`id`;
SELECT 1 FROM assessment_user_data, submissions WHERE assessment_user_data.latest_submission_id = submissions.id AND assessment_user_data.course_user_datum_id <> submissions.course_user_datum_id; SELECT 1 FROM assessment_user_data WHERE FALSE;
SELECT attachments.id, attachments.course_id FROM attachments; SELECT attachments.id, courses.id FROM attachments, assessments, courses WHERE attachments.assessment_id = assessments.id AND assessments.course_id = courses.id;
SELECT 1 FROM submissions, assessments, course_user_data WHERE submissions.assessment_id = assessments.id AND submissions.course_user_datum_id = course_user_data.id AND assessments.course_id <> course_user_data.course_id; SELECT 1 FROM submissions WHERE FALSE;
SELECT watchlist_instances.id, watchlist_instances.course_id FROM watchlist_instances; SELECT watchlist_instances.id, course_user_data.course_id FROM watchlist_instances, course_user_data WHERE watchlist_instances.course_user_datum_id = course_user_data.id;

-- These columns are nullable in the schema, but the application never stores nulls in them.
SELECT 1 FROM `submissions` WHERE `submissions`.`course_user_datum_id` IS NULL; SELECT 1 FROM `submissions` WHERE FALSE;
SELECT 1 FROM `assessments` WHERE `assessments`.`course_id` IS NULL; SELECT 1 FROM `assessments` WHERE FALSE;
